# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

from weakref import WeakKeyDictionary
from functools import partial
from itertools import count
import ctypes
import numpy as np

import jax
from jax.lib import xla_client as xc
from jax.interpreters import mlir
from jax.interpreters import batching

from ... import Atom
from ...native_function import IdxRepTy, ScalarType, RectContArrayType
from ... import api

def primitive(f):
  if not isinstance(f, Atom):
    raise TypeError("DexPrimitive expects a function atom as an argument")
  return partial(dex_apply_p.bind, func_atom=f)

compiler_cache = WeakKeyDictionary()
def get_compiled(func_atom):
  compiled = compiler_cache.get(func_atom, None)
  if compiled is None:
    compiled = compiler_cache[func_atom] = func_atom.compile(calling_convention='xla')
  return compiled


dex_apply_p = jax.core.Primitive('dex_apply')

@dex_apply_p.def_impl
def dex_call_impl(*args, func_atom):
  return get_compiled(func_atom)(*args)

# === abstract evaluation / shape inference ===

def dex_call_abstract_eval_with_shape(*args, func_atom):
  # TODO: Make it possible to get the signature without compiling the function
  native_func = get_compiled(func_atom)
  arg_sig = native_func.explicit_argument_signature
  res_sig = native_func.result_signature
  if len(args) != len(arg_sig):
    raise RuntimeError(f"Dex function expects {len(arg_sig)} arguments, but was given {len(args)}")
  if not all(isinstance(arg, jax.core.ShapedArray) for arg in args):
    raise RuntimeError("Cannot perform evaluation of Dex functions without known shapes")
  # Check arguments and infer shape parameters
  shape_vars = {}
  for i, (arg, b) in enumerate(zip(args, arg_sig)):
    expected_dtype = np.dtype(b.type.ctype)
    if arg.dtype != expected_dtype:
      raise RuntimeError(f"dtype mismatch in arg {i}: expected {expected_dtype}, got {arg.dtype}")
    if isinstance(b.type, ScalarType):
      expected_shape = ()
    elif isinstance(b.type, RectContArrayType):
      expected_shape = b.type.shape
    else:
      raise AssertionError("Unhandled case!")
    if len(arg.shape) != len(expected_shape):
      raise RuntimeError(f"rank mismatch in arg {i}: expected {len(expected_shape)}, got {len(arg.shape)}")
    inferred_shape = tuple(
      size if isinstance(size, int) else shape_vars.setdefault(size, real_size)
      for size, real_size in zip(expected_shape, arg.shape))
    if arg.shape != inferred_shape:
      raise RuntimeError(f"shape mismatch in arg {i}: expected {inferred_shape}, got {arg.shape}")
  # Infer result types
  result_avals = []
  for b in res_sig:
    dtype = np.dtype(b.type.ctype)
    if isinstance(b.type, ScalarType):
      shape = ()
    elif isinstance(b.type, RectContArrayType):
      shape = tuple(shape_vars.get(size, size) for size in b.type.shape)
    result_avals.append(jax.core.ShapedArray(shape, dtype))
  assert len(result_avals) == 1  # TODO: Make dex_call a multiple_results primitive
  return result_avals[0], shape_vars

@dex_apply_p.def_abstract_eval
def dex_call_abstract_eval(*args, **kwargs):
  return dex_call_abstract_eval_with_shape(*args, **kwargs)[0]

# === xla translation ===

PyCapsule_Destructor = ctypes.CFUNCTYPE(None, ctypes.py_object)
PyCapsule_New = ctypes.pythonapi.PyCapsule_New
PyCapsule_New.restype = ctypes.py_object
PyCapsule_New.argtypes = (ctypes.c_void_p, ctypes.c_char_p, PyCapsule_Destructor)

def make_custom_call_target(func_ptr):
  return PyCapsule_New(func_ptr, b"xla._CUSTOM_CALL_TARGET", PyCapsule_Destructor(0))

trampoline_custom_call_name = None
def get_trampoline():
  global trampoline_custom_call_name
  if trampoline_custom_call_name is not None:
    return trampoline_custom_call_name
  trampoline_custom_call_name = "dex_xla_cpu_trampoline"
  xc.register_custom_call_target(
      trampoline_custom_call_name.encode('ascii'),
      make_custom_call_target(api.xlaCpuTrampoline))
  return trampoline_custom_call_name

def dex_apply_lowering(ctx, *args, func_atom):
  native = get_compiled(func_atom)
  custom_call_name = get_trampoline()
  ctx.module_context.add_keepalive(native)

  # TODO: Support inference of implicit arguments. Abstract eval already does inference!
  if len(native.argument_signature) != len(native.explicit_argument_signature):
    raise NotImplementedError("Inference of implicit arguments")
  assert len(args) == len(native.explicit_argument_signature)

  native_ptr = mlir.ir_constant(
      ctypes.cast(native._as_parameter_, ctypes.c_void_p).value,
      canonicalize_types=False)
  result_type = [mlir.aval_to_ir_type(a) for a in ctx.avals_out]
  multi_result = len(ctx.avals_out) > 1
  if multi_result:
    result_type = [mlir.ir.TupleType.get_tuple(result_type)]
  custom_call = mlir.mhlo.CustomCallOp(
      result_type,
      (native_ptr, *args),
      call_target_name=mlir.ir.StringAttr.get(custom_call_name),
      has_side_effect=mlir.ir.BoolAttr.get(False),
      api_version=mlir.i32_attr(2),
      called_computations=mlir.ir.ArrayAttr.get([]),
      backend_config=mlir.ir.StringAttr.get(""),
      operand_layouts=None,
      result_layouts=None)
  if multi_result:
    return [mlir.mhlo.GetTupleElementOp(custom_call.result, mlir.i32_attr(i)).result
            for i in range(len(ctx.avals_out))]
  else:
    return custom_call.result,
mlir.register_lowering(dex_apply_p, dex_apply_lowering, platform='cpu')


# === batching ===

def dex_call_batched(batched_args, batched_dims, func_atom):
  """Batching function for dex primitives.

  Args:
    batched_args: The possibly-batched arguments.
    batched_dims: A sequence of the same length as `batched_args`, where each
      entry indicates the batching axis of the corresponding entry to `args`,
      or None if that argument should not be batched. Not all entries can be
      None.

  Returns:
    2-tuple containing the result of the batched function, and the result axis
    which was batched, which is always zero.
  """
  module = func_atom.module.copy()

  # Move axes so that we only have to deal with the zero axis being batched.
  uniform_batched_args = [
      batching.moveaxis(arg, bd, 0) if bd is not batching.not_mapped else arg
      for arg, bd in zip(batched_args, batched_dims)
  ]

  # This assumes not all entries in batched_dims are None.
  batch_size = next(
      arg.shape[0] for arg, bd in zip(uniform_batched_args, batched_dims)
      if bd is not batching.not_mapped)

  # Add the current function atom as a variable in the context, so that we can
  # use it to apply batching.
  func_name = func_atom.name
  assert func_name is not None

  # Only index into the arguments which are batched. `i` is the index used for
  # the Dex for loop constructor.
  batched_fn_params = [
      f"x{param_idx}" if dim is batching.not_mapped else f"x{param_idx}.i"
      for param_idx, dim in enumerate(batched_dims)
  ]

  # This is the actual batching expression
  batched_fn = module.eval(
      r"\ " + " ".join(f"x{i}" for i in range(len(batched_args))) + ". "
      + f"for i:(Fin {batch_size}). {func_name} "
      + " ".join(batched_fn_params))

  return primitive(batched_fn)(*uniform_batched_args), 0


batching.primitive_batchers[dex_apply_p] = dex_call_batched


# === jvp / linearize  ===

def dex_call_jvp(arg_values, arg_tangents, func_atom):
  """Evaluates the function output at arg_values, and the linearized function
  (linearized about arg_values) at arg_tangents.

  Args:
    arg_values: A tuple of arguments.
    arg_tangents: A tuple with the tangents of the arguments. The tuple has the
      same length as the arg_values. Some of the tangents may also be the
      special value ad.Zero to specify a zero tangent.
    func_atom: Function atom to linearize. The result type of this function
      atom must be a single array type.

  Returns:
     A pair of the primal output and the tangent.
  """
  assert len(func_atom.compile().result_signature) == 1
  num_args = len(arg_values)
  module = func_atom.module.copy()

  # Helper functions to build strings of primal and tangent inputs.
  def arg_string(prefix):
    return " ".join(f"{prefix}{i}" for i in range(num_args))

  def tuple_string(prefix):
    return "(" + ", ".join(f"{prefix}{i}" for i in range(num_args)) + ")"

  # Add the current function atom as a variable in the context, so that we can
  # use it to apply batching.

  jax_func_name = func_atom.name
  assert jax_func_name is not None

  # `linearize` only seems to work properly for functions which take a single
  # input argument, so we uncurry `func_atom` to make it into this form. The
  # evaluated string for three function arguments should look like:
  # ```
  # \ (x0, x1, x2). jax_func x0 x1 x2
  # ```
  uncurried = module.eval(
      f"\\ {tuple_string('x')}. {jax_func_name} {arg_string('x')}")
  jax_func_uncurried_name = uncurried.name
  assert jax_func_uncurried_name is not None

  # We create separate primitives for the primal and tangent evaluations, since
  # we only want to apply tranposition to the tangent evaluation function.
  #
  # Here we write out the tangent evaluation expression in pointful style.
  # The evaluated string for three function arguments should look like:
  # ```
  # \ x0 x1 x2 u0 u1 u2.
  #   linearized = linearize jax_func_uncurried (x0, x1, x2)
  #   snd linearized (u0 u1 u2)
  # ```
  evaluate_linearized = module.eval(
      f"\\ {arg_string('x')} {arg_string('u')}." +
      f"\n  linearized = linearize {jax_func_uncurried_name} {tuple_string('x')}" +
      f"\n  snd linearized {tuple_string('u')}")

  # Materialize jax.ad.Zero values into actual arrays of zeros.
  # TODO: Make the handling of Zeros more efficient by omitting them from the
  # linearize expression. This would avoid having to create these zero
  # arguments, although it might make constructing the transpose expression
  # more fiddly.
  tangents_no_zeros = [
      jax.lax.zeros_like_array(arg) if type(tan) is jax.ad.Zero else tan
      for arg, tan in zip(arg_values, arg_tangents)
  ]

  return (
      primitive(func_atom)(*arg_values),
      primitive(evaluate_linearized)(*arg_values, *tangents_no_zeros),
  )

jax.interpreters.ad.primitive_jvps[dex_apply_p] = dex_call_jvp

# === transpose ===

# alias to avoid confusion around overloading of "primal".
_is_linear_input = jax.ad.is_undefined_primal


def dex_call_evaluate_linearized_transpose(cotangents, *args, func_atom):
  """Evaluates the transpose of a function atom.  """

  # `func_atom` is assumed to be of the form of `evaluate_linearized` from
  # `dex_call_jvp`, applied to a some function atom, called `f`, say.
  # Concretely, if `f` has three primal arguments, `func_atom` should look like:
  # ```
  # \ x0 x1 x2 u0 u1 u2.
  #   intermediate_linearized = linearize f (x0, x1, x2)
  #   snd intermediate_linearized (u0 u1 u2)
  # ```
  # In particular, its arguments are assumed to be `num_primals` primal inputs,
  # followed by `num_primals` tangent inputs.

  assert len(args) % 2 == 0
  num_primals = len(args) // 2
  module = func_atom.module.copy()

  primals, tangents = args[:num_primals], args[num_primals:]

  # Helper functions to build strings of primal and tangent inputs.
  def arg_string(prefix, index_set):
    return " ".join(f"{prefix}{i}" for i in index_set)

  def tuple_string(prefix, index_set):
    return "(" + ", ".join(f"{prefix}{i}" for i in index_set) + ")"

  # JAX uses `UndefinedPrimal` instances to mark input variables which the
  # function needs to be transposed with respect to, and (consequently) for
  # which no concrete values are available. `_is_linear_input` tests if the
  # input is such an instance.
  #
  # `func_atom` is only guaranteed to be linear in its tangent inputs, so we
  # check here that we're not expected to tranpose it with respect to any primal
  # inputs. JAX *should* take care of this automatically, but this mechanism is
  # somewhat poorly documented so its worth double checking.
  if any(_is_linear_input(p) for p in primals):
    raise RuntimeError("Primal inputs to transpose primitive are undefined.")

  # Add `func_atom` as a variable `linearized` in the context.
  linearized_name = func_atom.name
  assert linearized_name is not None

  # Form lists of the indices in `tangents` which correspond to linear inputs
  # (which we are expected to transpose w.r.t.) and constant inputs (which we
  # are not). The constant inputs will be exactly the arrays of zeros which are
  # instantiated in the JVP in response to a `Zero` argument.
  tangent_input_indices = [
      i for i, t in enumerate(tangents) if _is_linear_input(t)
  ]
  tangent_constant_indices = [
      i for i, t in enumerate(tangents) if not _is_linear_input(t)
  ]

  # In this case, there are no cotangents to output. Not sure if JAX would skip
  # calling this function in this case or not.
  if len(tangent_input_indices) == 0:
    return (None,) * len(args)

  # Form a lambda which partially evaluates `linearized` at the constant primal
  # and constant tangent values, with the remaining arguments (i.e. the linear
  # input tangents) combined into a tuple, and then transpose the lambda.
  #
  # For a three-input primal function with constant input for the tangent
  # parameter at index 1, the evaluated string should look like:
  # ```
  # \ x0 x1 x2 u1 ct.
  #   transpose_linear (\(t0, t2). linearized x0 x1 x2 t0 u1 t2) ct
  # ```
  # - The `x` variables are the (constant) inputs to the primal function. These
  #   should always be supplied by JAX.
  # - The `u` variables are the constant tangent inputs, i.e. those which JAX
  #   does not need us to include in the transpose.
  # - The `t` variables are the linear inputs which we are transposing with
  #   respect to. These are tangent inputs to `linearized`.

  # x0 x1 x2 u1 ct
  transposed_atom_params = (
      arg_string("x", range(num_primals)) + " " +
      arg_string("u", tangent_constant_indices) + " ct")

  # (t0, t2)
  linear_lambda_params = tuple_string("t", tangent_input_indices)

  # t0 u1 t2
  linearized_tangent_inputs = (" ".join(
      f"t{i}" if jax.ad.is_undefined_primal(t) else f"u{i}"
      for i, t in enumerate(tangents)))

  # x0 x1 x2 t0 u1 t2
  linearized_inputs = (
      arg_string("x", range(num_primals)) + " " + linearized_tangent_inputs)

  # \ x0 x1 x2 u1 ct.
  #   transpose_linear (\(t0, t2). linearized x0 x1 x2 t0 u1 t2) ct
  transposed = module.eval(
      f"\\ {transposed_atom_params}. transpose_linear " +
      f"(\ {linear_lambda_params}. {linearized_name} {linearized_inputs}) ct"
  )

  # Tuple of cotangents relating to linear tangent inputs. In the given
  # example, this would be a tuple of the two cotangents relating to inputs 0
  # and 2.
  resulting_cotangents = primitive(transposed)(
      *primals, *[tangents[i] for i in tangent_constant_indices], cotangents)

  # If there is only one resulting cotangent, we need to make it into a tuple
  # so we can still zip over it.
  if len(tangent_input_indices) == 1:
    resulting_cotangents = (resulting_cotangents,)

  # Pack the output with `None`s where the inputs are constants, as required by
  # JAX.
  result = [None] * len(args)
  for ct_idx, ct in zip(tangent_input_indices, resulting_cotangents):
    result[num_primals + ct_idx] = ct

  return tuple(result)

jax.interpreters.ad.primitive_transposes[dex_apply_p] = dex_call_evaluate_linearized_transpose
