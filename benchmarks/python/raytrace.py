# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

from collections import namedtuple
from functools import partial
from os import environ
import time

import matplotlib as mpl
import matplotlib.pyplot as plt
import jax.numpy as np
import jax.lax as lax
import jax.random as random
from jax import vmap, jit, pmap
from jax.tree_util import tree_map, tree_multimap

from jax.config import config
config.update("jax_enable_x64", True)
config.enable_omnistaging()

def length(x): return np.sqrt(np.dot(x, x))
def normalize(x): return x / length(x)
def relu(x): return np.maximum(x, 0.0)

def cross(a, b):
  (a1, a2, a3) = a
  (b1, b2, b3) = b
  return np.array([a2 * b3 - a3 * b2, a3 * b1 - a1 * b3, a1 * b2 - a2 * b1])

def directionAndLength(x):
  l = length(x)
  return (x / length(x), l)

def rotateX(p, angle):
  c = np.cos(angle)
  s = np.sin(angle)
  (px, py, pz) = p
  return np.array([px, c*py - s*pz, s*py + c*pz])

def rotateY(p, angle):
  c = np.cos(angle)
  s = np.sin(angle)
  (px, py, pz) = p
  return np.array([c*px + s*pz, py, - s*px+ c*pz])

def rotateZ(p, angle):
  c = np.cos(angle)
  s = np.sin(angle)
  (px, py, pz) = p
  return np.array([c*px - s*py, s*px+c*py, pz])

def sampleCosineWeightedHemisphere(normal, k):
  (k1, k2) = random.split(k)
  u1 = random.uniform(k1)
  u2 = random.uniform(k2)
  uu = normalize (cross(normal, np.array([0.0, 1.1, 1.1])))
  vv = cross(uu, normal)
  ra = np.sqrt(u2)
  rx = ra * np.cos (2.0 * np.pi * u1)
  ry = ra * np.sin (2.0 * np.pi * u1)
  rz = np.sqrt (1.0 - u2)
  rr = (rx * uu) + (ry * vv) + (rz * normal)
  return normalize(rr)

def positiveProjection(x, y):
  assert x.shape == (3,)
  assert y.shape == (3,), y
  return np.dot(x, y) > 0.0

# TODO: use AD instead
def gradNumerical(f, xs):
  eps = 0.0001
  n, = xs.shape
  return vmap(lambda delta: (f(xs + delta) - f (xs - delta)) / (2.0 * eps))(eps * np.eye(n))

xHat = np.array([1.0, 0.0, 0.0], dtype=np.float64)
yHat = np.array([0.0, 1.0, 0.0], dtype=np.float64)
zHat = np.array([0.0, 0.0, 1.0], dtype=np.float64)

def dummy_float_vec(n):
  return np.array([np.nan]*n, dtype=np.float64)

dummy_color = dummy_float_vec(3)
dummy_pos   = dummy_float_vec(3)
dummy_dir   = dummy_float_vec(3)

# Wall Block Sphere
ObjectGeom = namedtuple("ObjectGeom",
                        ["tag",
                         "wallDirection", "wallDistance",
                         "blockPos", "blockHW", "blockAngle",
                         "spherePos", "sphereRadius"])

dummy_object_geom = ObjectGeom(-1,
                               dummy_dir, 0.0,
                               dummy_pos, dummy_float_vec(3), 0.0,
                               dummy_pos, 0.0)

WALL_OBJECT   = 0
BLOCK_OBJECT  = 1
SPHERE_OBJECT = 2

def make_wall(wallDirection, wallDistance):
  geom = dummy_object_geom
  geom = geom._replace( tag = WALL_OBJECT
                      , wallDirection = wallDirection
                      , wallDistance  = wallDistance)
  return geom

def make_block(blockPos, blockHW, blockAngle):
  geom = dummy_object_geom
  geom = geom._replace( tag = BLOCK_OBJECT
                      , blockPos   = blockPos
                      , blockHW    = blockHW
                      , blockAngle = blockAngle)
  return geom

def make_sphere(spherePos, sphereRadius):
  geom = dummy_object_geom
  geom = geom._replace(  tag = SPHERE_OBJECT
                       , spherePos    = spherePos
                       , sphereRadius = sphereRadius)
  return geom

Surface = namedtuple("Surface", ["tag", "matteColor"])

dummy_surface = Surface(0, dummy_color)

MATTE = 0
MIRROR = 1

def make_matte(color):
  return Surface(MATTE, color)

def make_mirror():
  return Surface(MIRROR, dummy_color)

Obj = namedtuple("Obj",
                 ["tag",
                 "passiveGeom", "passiveSurface",
                 "lightPos", "lightHW", "lightRadiance"])

dummy_object = Obj(-1, dummy_object_geom, dummy_surface, dummy_pos, 0.0, dummy_color)

PASSIVE_OBJECT = 0
LIGHT = 1

def make_passive_object(passiveGeom, passiveSurface):
  obj = dummy_object
  obj = obj._replace(tag=PASSIVE_OBJECT, passiveGeom=passiveGeom,
                    passiveSurface=passiveSurface)
  return obj

def make_light(lightPos, lightHW, lightRadiance):
  obj = dummy_object
  obj = obj._replace(tag=LIGHT, lightPos=lightPos,
                     lightHW=lightHW,lightRadiance=lightRadiance)
  return obj

def sampleReflection(nor_surf, ray, k):
  (pos, dir) = ray
  (nor, surf) = nor_surf
  def matteCase(_): return sampleCosineWeightedHemisphere(nor, k)
  def mirrorCase(_): return dir - (2.0 * np.dot(dir, nor)) * nor
  newRay = lax.switch(surf.tag, [matteCase, mirrorCase], ())
  return (pos, newRay)

def probReflection(nor_surf, _, ray):
  (nor, surf) = nor_surf
  (_, outRayDir) = ray
  def matteCase(_): return relu (np.dot(nor, outRayDir))
  def mirrorCase(_): return 0.0
  return lax.switch(surf.tag, [matteCase, mirrorCase], ())

def applyFilter(filter, radiance): return filter * radiance

def surfaceFilter(filter, surf):
  def matteCase(_):  return filter * surf.matteColor
  def mirrorCase(_): return filter
  return lax.switch(surf.tag, [matteCase, mirrorCase], ())

def sdObj(pos, obj):
  def passiveObjCase(_):
    geom = obj.passiveGeom
    def wallCase(_):
      (nor, d) = (geom.wallDirection, geom.wallDistance)
      return d + np.dot(nor, pos)
    def blockCase(_):
      blockPos, halfWidths, angle = (geom.blockPos, geom.blockHW, geom.blockAngle)
      relPos = rotateY(pos - blockPos, angle)
      return length(np.maximum(np.abs(relPos) - halfWidths, 0.0))
    def sphereCase(_):
      spherePos, r = (geom.spherePos, geom.sphereRadius)
      relPos = pos - spherePos
      return np.maximum(length(relPos) - r, 0.0)
    return lax.switch(geom.tag, [wallCase, blockCase, sphereCase], ())
  def lightCase(args):
    (squarePos, hw) = (obj.lightPos, obj.lightHW)
    relPos = pos - squarePos
    halfWidths = np.array([hw, 0.01, hw])
    return length(np.maximum(np.abs(relPos) - halfWidths, 0.0))
  return lax.switch(obj.tag, (passiveObjCase, lightCase), ())

def sdScene(scene, pos):
  distances = vmap(partial(sdObj, pos))(scene)
  d = np.min(distances)
  i = np.argmin(distances)
  return (tree_map(lambda x: x[i], scene), d)

def calcNormal(scene, pos):
  dist = lambda p: sdScene(scene, p)[1]
  return normalize(gradNumerical(dist, pos))

RayMarchResult = namedtuple("RayMarchResult", ["tag", "ray", "surf", "radiance"])
dummy_oriented_surface = (dummy_dir, dummy_surface)
dummy_raymarch_result = RayMarchResult(-1, (dummy_pos, dummy_dir),
                                       dummy_oriented_surface, dummy_color)

HIT_OBJ = 0
HIT_LIGHT = 1
HIT_NOTHING = 2

def make_hit_obj(ray, surf):
  ans = dummy_raymarch_result
  ans = ans._replace(tag=HIT_OBJ, ray=ray, surf=surf)
  return ans

def make_hit_light(radiance):
  ans = dummy_raymarch_result
  ans = ans._replace(tag=HIT_LIGHT, radiance=radiance)
  return ans

def make_hit_nothing():
  ans = dummy_raymarch_result
  ans = ans._replace(tag=HIT_NOTHING)
  return ans

def raymarch(scene, ray):
  max_iters = 100
  tol = 0.01
  startLength = 10.0 * tol
  (rayOrigin, rayDir) = ray
  err_init = 100000.0
  def cond(i_err_result_rayLength):
    (i, err, _, rayLength) = i_err_result_rayLength
    def false_case(_):
      rayPos = rayOrigin + rayLength * rayDir
      surfNorm = calcNormal(scene, rayPos)
      return positiveProjection(rayDir, surfNorm)
    return lax.cond(np.logical_and(i < max_iters, err >= tol),
                    lambda _: True, false_case, ())

  def body(i_err_result_rayLength):
    (i, _, _, rayLength) = i_err_result_rayLength
    rayPos = rayOrigin + rayLength * rayDir
    (obj, d) = sdScene(scene, rayPos)
    # 0.9 ensures we come close to the surface but don't touch it
    rayLengthNew = rayLength + 0.9 * d
    def passiveCase(_):
      surfNorm = calcNormal(scene, rayPos)
      return make_hit_obj((rayPos, rayDir), (surfNorm, obj.passiveSurface))
    def lightCase(_):
      return make_hit_light(obj.lightRadiance)
    raymarchResult = lax.switch(obj.tag, [passiveCase, lightCase], ())
    return (i + 1, d, raymarchResult, rayLengthNew)

  (_, _, result, _) = lax.while_loop(
    cond, body, (0, err_init, make_hit_nothing(), 0.0))
  return result

zero_radiance = np.array([0.0, 0.0, 0.0], dtype=np.float64)

def rayDirectRadiance(scene, ray):
  ans = raymarch(scene, ray)
  return np.where(ans.tag == HIT_LIGHT,
                  ans.radiance, zero_radiance)

def sampleSquare(hw, k):
 (kx, kz) = random.split(k)
 x = random.uniform(kx, minval= -hw, maxval=hw)
 z = random.uniform(kz, minval= -hw, maxval=hw)
 return np.array([x, 0.0, z])

def num_scene_objects(scene):
  cell = lambda: None
  def record_shape(xs):
    cell.contents = xs.shape
  tree_map(record_shape, scene)
  return cell.contents[0]

def sampleLightRadiance(scene, osurf, inRay, k):
  (surfNor, surf) = osurf
  (rayPos, _) = inRay
  def body(i, total):
    obj = tree_map(lambda x: x[i], scene)
    def passive_case(_):
      return zero_radiance
    def light_case(_):
      (lightPos, hw) = (obj.lightPos, obj.lightHW)
      (dirToLight, distToLight) = directionAndLength(lightPos + sampleSquare(hw, k) - rayPos)
      def this_side_case(_):
        fracSolidAngle = relu(np.dot(dirToLight, yHat)) * (hw**2) / (np.pi * (distToLight**2))
        outRay = (rayPos, dirToLight)
        coeff = fracSolidAngle * probReflection(osurf, inRay, outRay)
        return coeff * rayDirectRadiance(scene, outRay)
      def far_side_case(_):
        return zero_radiance
      return lax.cond(positiveProjection(dirToLight, surfNor), this_side_case, far_side_case, ())
    radiance = lax.switch(obj.tag, [passive_case, light_case], ())
    return total + radiance
  return lax.fori_loop(0, num_scene_objects(scene), body, zero_radiance)

dummy_ray    = (np.zeros((3,)), np.zeros((3,)))
dummy_filter = np.zeros((3,))

def trace(params, scene, init_ray, k):
  (_, max_bounces, _) = params
  noFilter = np.array([1.0, 1.0, 1.0])

  def while_cond(args):
    (i, (finished, _, _, _)) = args
    return np.logical_and(i < max_bounces, np.logical_not(finished))

  def while_body(args):
    (i, (_, color_filter, total_radiance, cur_ray)) = args
    raymarchResult = raymarch(scene, cur_ray)
    def hitObjCase(_):
      (incidentRay, osurf) = (raymarchResult.ray, raymarchResult.surf)
      (k1, k2) = random.split(random.fold_in(k, i))
      lightRadiance    = sampleLightRadiance(scene, osurf, incidentRay, k1)
      outRayHemisphere = sampleReflection          (osurf, incidentRay, k2)
      newFilter = surfaceFilter(color_filter, osurf[1])
      newRadiance = total_radiance + applyFilter(newFilter, lightRadiance)
      return (False, newFilter, newRadiance, outRayHemisphere)
    def hitLightCase(_):
      radiance = np.where(i == 0, raymarchResult.radiance, total_radiance)
      return (True, dummy_filter, radiance, dummy_ray)
    def hitNothingCase(_):
      return (True, color_filter, total_radiance, cur_ray)
    result = lax.switch(raymarchResult.tag, [hitObjCase, hitLightCase, hitNothingCase], ())
    return (i + 1, result)

  loop_init = (0, (False, np.array([1.0,1.0,1.0]), np.array([0.0,0.0,0.0]), init_ray))
  (_, (_, _, total, _)) = lax.while_loop(while_cond, while_body, loop_init)
  return total

class WrapList(object):
  def __init__(self, x):
    self.contents = x

def zipNestedNamedTuples(records):
  ls = tree_map(lambda _: WrapList([]), records[0])
  for record in records:
    def f(l, x): l.append(x)
    tree_multimap(lambda l, x: l.contents.append(x), ls, record)
  return tree_map(lambda l: np.array(l.contents), ls)

Pixel = namedtuple("Pixel", ["xmin", "xmax", "ymin", "ymax"])

def pixel_positions(camera):
  (n, _, halfWidth, _) = camera
  pixHalfWidth = halfWidth / n
  ys = np.broadcast_to(np.flip(np.linspace(-halfWidth, halfWidth, n))[:, None], (n, n))
  xs = np.broadcast_to(        np.linspace(-halfWidth, halfWidth, n )[None, :], (n, n))
  return Pixel(xs - pixHalfWidth, xs + pixHalfWidth,
               ys - pixHalfWidth, ys + pixHalfWidth)

def pixelColor(params, camera, pix_positions, scene, k, i, j):
  (n, pos, halfWidth, sensorDist) = camera
  pixHalfWidth = halfWidth / n
  (k1, k2) = random.split(k)
  (kx, ky) = random.split(k1)
  pix = tree_map(lambda arr: arr[i, j], pix_positions)
  x = random.uniform(kx, minval=pix.xmin, maxval=pix.xmax)
  y = random.uniform(ky, minval=pix.ymin, maxval=pix.ymax)
  ray = (pos, normalize(np.array([x, y, -sensorDist])))
  return trace(params, scene, ray, k2)

def pixelColorAvg(params, camera, pix_positions, scene, k_root, i, j):
  (num_samples, _, _) = params
  ks = random.split(k_root, num=num_samples)
  assert ks.shape == (num_samples, 2)
  ans = vmap(lambda k: pixelColor(params, camera,
                                  pix_positions, scene, k, i, j))(ks)
  return np.mean(ans, axis=0)

def timeit(f):
  t0 = time.time()
  ans = f()
  print("{} seconds".format(time.time() - t0))
  return ans

num_pix = 32
num_samples = 8
num_bounces = 10
share_prng = True

params = (num_samples, num_bounces, share_prng)
camera = (num_pix, 10.0 * zHat, 0.3, 1.0)

lightColor = np.array([0.2, 0.2, 0.2])
leftWallColor  = 1.5 * np.array([0.611, 0.0555, 0.062])
rightWallColor = 1.5 * np.array([0.117, 0.4125, 0.115])
whiteWallColor = np.array([255.0, 239.0, 196.0]) / 255.0
blockColor     = np.array([200.0, 200.0, 255.0]) / 255.0

theScene = zipNestedNamedTuples(
    [ make_light(1.9 * yHat, 0.5, lightColor)
    , make_passive_object(make_wall(  xHat, 2.0), make_matte(leftWallColor))
    , make_passive_object(make_wall(- xHat, 2.0), make_matte(rightWallColor))
    , make_passive_object(make_wall(  yHat, 2.0), make_matte(whiteWallColor))
    , make_passive_object(make_wall(- yHat, 2.0), make_matte(whiteWallColor))
    , make_passive_object(make_wall(  zHat, 2.0), make_matte(whiteWallColor))
    , make_passive_object(make_block(np.array([ 1.0, -1.6,  1.2]),
                                     np.array([0.6, 0.8, 0.6]), 0.5),
                          make_matte(blockColor))
    , make_passive_object(make_sphere(np.array([-1.0, -1.2,  0.2]), 0.8),
                          make_matte(0.7 * whiteWallColor))
    , make_passive_object(make_sphere(np.array([ 2.0,  2.0, -2.0]), 1.5),
                          make_mirror())
    ])

pix_positions = pixel_positions(camera)

xidxs = np.broadcast_to(np.arange(num_pix)[None, :], (num_pix, num_pix))
yidxs = np.broadcast_to(np.arange(num_pix)[:, None], (num_pix, num_pix))

num_cores = 32
def tile_cores(arr):
  assert arr.shape[0] % num_cores == 0
  size = arr.shape[0] // num_cores
  return np.reshape(arr, (num_cores,size) + arr.shape[1:])

def untile_cores(arr):
  assert arr.shape[0] == num_cores
  num_tiles = arr.shape[1]
  return np.reshape(arr, (num_cores * num_tiles,) + arr.shape[2:])

@jit
def renderScene_pmap(yidxs, xidxs):
  return untile_cores(pmap(vmap(vmap(
    partial(pixelColorAvg, params, camera, pix_positions,
            theScene, random.PRNGKey(0)))))(tile_cores(yidxs), tile_cores(xidxs)))

@jit
def renderScene_no_pmap(yidxs, xidxs):
  return vmap(vmap(
    partial(pixelColorAvg, params, camera, pix_positions,
            theScene, random.PRNGKey(0))))(yidxs, xidxs)

using_gpu = not environ.get("CUDA_VISIBLE_DEVICES") == ""

if using_gpu:
  renderScene = renderScene_no_pmap
else:
  renderScene = renderScene_pmap

print("Compile time + run time")
img1 = timeit(lambda: renderScene(yidxs, xidxs).block_until_ready())

print("Run time")
img2 = timeit(lambda: renderScene(yidxs, xidxs).block_until_ready())

img = img2 / np.mean(img2)

plt.imshow(img, interpolation='none')
plt.grid('off')
plt.axis('off')
plt.savefig("jax-render.png")
