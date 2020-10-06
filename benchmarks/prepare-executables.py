import sys
import os
import struct
from pathlib import Path
from itertools import product

RODINIA_ROOT = Path('rodinia') / 'rodinia'
PARBOIL_DATA_ROOT = Path('parboil') / 'data'
if not RODINIA_ROOT.exists():
  print("Rodinia benchmark suite missing. Please download it and place it in a "
        "`rodinia/rodinia` subdirectory.")
  sys.exit(1)
if not PARBOIL_DATA_ROOT.exists():
  print("Parboil benchmark suite missing. Please download the datasets and place them "
        "in a `parboil/data` subdirectory.")
  sys.exit(1)

EXE_ROOT = Path('exe')
RODINIA_EXE_ROOT = EXE_ROOT / 'rodinia'
PARBOIL_EXE_ROOT = EXE_ROOT / 'parboil'

# TODO: An easy way to do this would be to wrap the parameters in arrays, but
#       that doesn't work when the return type depends on any of them.
PREVENT_PARAMETER_INLINING = True
PRINT_OUTPUTS = False

def prepare_rodinia_kmeans():
  kmeans_data_path = RODINIA_ROOT / 'data' / 'kmeans'
  kmeans_data_files = [
    (kmeans_data_path / '100', 10),
    (kmeans_data_path / '204800.txt', 8),
    (kmeans_data_path / 'kdd_cup', 5),
  ]

  kmeans_exe_path = RODINIA_EXE_ROOT / 'kmeans'
  kmeans_exe_path.mkdir(parents=True, exist_ok=True)

  for (df, k) in kmeans_data_files:
    with open(df, 'r') as f:
      lines = [l for l in f.read().split('\n') if l]
      vals = [map(ensure_float, l.split()[1:]) for l in lines]
    case_exe_path = kmeans_exe_path / (df.stem + '.dx')
    with open(case_exe_path, 'w') as f:
      emit_dex(f, 'rodinia', 'kmeans', [
          ('points', format_matrix(vals)),
          ('k', k),
          ('threshold', 0),
          ('max_iterations', 500),
        ])
    print(f'Created {case_exe_path}')

def prepare_rodinia_hotspot():
  data_path = RODINIA_ROOT / 'data' / 'hotspot'
  data_files = [(data_path / f'temp_{size}', data_path / f'power_{size}', size)
                for size in (64, 512, 1024)]
  exe_path = RODINIA_EXE_ROOT / 'hotspot'
  exe_path.mkdir(parents=True, exist_ok=True)

  for (tf, pf, size) in data_files:
    with open(tf, 'r') as f:
      tvals = [l for l in f.read().split('\n') if l]
    with open(pf, 'r') as f:
      pvals = [l for l in f.read().split('\n') if l]
    ts = list(chunk(tvals, size))
    ps = list(chunk(pvals, size))

    case_exe_path = exe_path / f'{size}.dx'
    with open(case_exe_path, 'w') as f:
      emit_dex(f, 'rodinia', 'hotspot', [
          ('numIterations', 360),
          ('T', format_matrix(ts)),
          ('P', format_matrix(ps))
        ])
      print(f'Created {case_exe_path}')

def prepare_rodinia_backprop():
  exe_path = RODINIA_EXE_ROOT / 'backprop'
  exe_path.mkdir(parents=True, exist_ok=True)
  exe_path_ad = RODINIA_EXE_ROOT / 'backprop-ad'
  exe_path_ad.mkdir(parents=True, exist_ok=True)
  in_features = [512, 123]

  for inf, use_ad in product(in_features, (False, True)):
    outf = 1
    hidf = 16
    case_exe_path = (exe_path_ad if use_ad else exe_path) / f'{inf}_{hidf}_{outf}.dx'
    with open(case_exe_path, 'w') as f:
      emit_dex(f, 'rodinia', 'backprop', [
          ('input', random_vec('in=>Float')),
          ('target', random_vec('out=>Float')),
          ('inputWeights', random_mat('{ b: Unit | w: in }=>hid=>Float')),
          ('hiddenWeights', random_mat('{ b: Unit | w: hid }=>out=>Float')),
          ('oldInputWeights', random_mat('{ b: Unit | w: in }=>hid=>Float')),
          ('oldHiddenWeights', random_mat('{ b: Unit | w: hid }=>out=>Float')),
        ], preamble=[
          ('in', f'Fin {inf}'),
          ('hid', f'Fin {hidf}'),
          ('out', f'Fin {outf}'),
        ])
      print(f'Created {case_exe_path}')

def prepare_rodinia_pathfinder():
  exe_path = RODINIA_EXE_ROOT / 'pathfinder'
  exe_path.mkdir(parents=True, exist_ok=True)
  world_sizes = [(100, 100000)]

  for rows, cols in world_sizes:
    case_exe_path = exe_path / f'{rows}_{cols}.dx'
    with open(case_exe_path, 'w') as f:
      emit_dex(f, 'rodinia', 'pathfinder', [
          ('world', random_mat(f'(Fin {rows})=>(Fin {cols})=>Int', gen='randInt')),
        ])
      print(f'Created {case_exe_path}')

def prepare_parboil_mriq():
  # NB: Run-time of this one shouldn't be data-dependent, so for now we just
  #     generate random inputs of sizes matching the standard dataset.
  exe_path = PARBOIL_EXE_ROOT / 'mriq'
  exe_path.mkdir(parents=True, exist_ok=True)
  problem_sizes = [
    (32768, 3072, 'small'),
    (262144, 2048, 'large'),
  ]

  for nx, nk, name in problem_sizes:
    case_exe_path = exe_path / (name + '.dx')
    with open(case_exe_path, 'w') as f:
      emit_dex(f, 'parboil', 'mriq', [
          *[(f'k{c}', random_vec(f'(Fin {nk})=>Float')) for c in ('x', 'y', 'z')],
          *[(f'{c}', random_vec(f'(Fin {nx})=>Float')) for c in ('x', 'y', 'z')],
          *[(f'{c}', random_vec(f'(Fin {nk})=>Float')) for c in ('r', 'i')],
        ])
    print(f'Created {case_exe_path}')

def prepare_parboil_stencil():
  exe_path = PARBOIL_EXE_ROOT / 'stencil'
  exe_path.mkdir(parents=True, exist_ok=True)
  problem_sizes = [
    (128, 128, 32),
    (512, 512, 64),
  ]

  for x, y, z in problem_sizes:
    case_exe_path = exe_path / f'{x}_{y}_{z}.dx'
    with open(case_exe_path, 'w') as f:
      emit_dex(f, 'parboil', 'stencil', [
        ('input', random_cube(f'(Fin {x})=>(Fin {y})=>(Fin {z})=>Float')),
      ])
    print(f'Created {case_exe_path}')

def prepare_parboil_histogram():
  df_root = PARBOIL_DATA_ROOT / 'histo'
  exe_path = PARBOIL_EXE_ROOT / 'histogram'
  exe_path.mkdir(parents=True, exist_ok=True)
  data_files = [
    (df_root / 'default' / 'input' / 'img.bin', 'default'),
    (df_root / 'large' / 'input' / 'img.bin', 'large'),
  ]

  for df, name in data_files:
    with open(df, 'rb') as f:
      stream = struct.iter_unpack('i', f.read())
      img_width, = next(stream)
      img_height, = next(stream)
      hist_width, = next(stream)
      hist_height, = next(stream)
      hist_size = hist_width * hist_height
      data = [str(v[0]) for v in stream]
      assert len(data) == img_width * img_height
      img = list(chunk(data, img_width))
      assert len(img) == img_height and len(img[0]) == img_width
    case_exe_path = exe_path / (name + '.dx')
    with open(case_exe_path, 'w') as f:
      emit_dex(f, 'parboil', 'histogram', [
          ('hist_size', hist_size),
          ('input', format_matrix(img)),
        ])
    print(f'Created {case_exe_path}')

def random_vec(ty, gen='rand'):
  return f'((for i. {gen} (ixkey (newKey 0) i)) : ({ty}))'

def random_mat(ty, gen='rand'):
  return f'((for i j. {gen} (ixkey (newKey 0) (i, j))) : ({ty}))'

def random_cube(ty, gen='rand'):
  return f'((for i j k. {gen} (ixkey (newKey 0) (i, j, k))) : ({ty}))'

def chunk(l, s):
  for i in range(0, len(l), s):
    yield l[i:i + s]

def emit_dex(f, suite, name, params, *, preamble=[]):
  for n, v in preamble:
    f.write(f'{n} = {v}\n')
  for n, v in params:
    f.write(f'{n} = {v}\n')
  f.write('\n')
  f.write(f'include "{suite}/{name}.dx"\n')
  f.write('\n')
  f.write(f'%bench "{name}"\n')
  f.write(f'result = {name} {(" ".join(n for n, v in params))}\n')
  if PRINT_OUTPUTS:
    f.write('\n')
    f.write('result\n')

def format_table(l, sep=','):
  return '[' + sep.join(l) + ']'

def format_matrix(m):
  return format_table((format_table(cols) for cols in m), sep=',\n  ')

def ensure_float(s):
  if '.' not in s:
    return s + ".0"
  return s

prepare_parboil_histogram()
prepare_parboil_stencil()
prepare_parboil_mriq()
prepare_rodinia_pathfinder()
prepare_rodinia_backprop()
# Verified outputs
prepare_rodinia_hotspot()
prepare_rodinia_kmeans()
