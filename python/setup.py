from setuptools import setup, find_packages
import os

# Check dex so file exists in dex directory.
so_file = "libDex.so"
dex_dir = os.path.join(os.path.dirname(__file__), 'dex')
if not os.path.exists(os.path.join(dex_dir, so_file)):
  raise FileNotFoundError(f"{so_file} not found in dex/, "
                          f"please run `make build-ffis`")

setup(
  name='dex',
  version='0.0.1',
  description='A research language for typed, functional array processing',
  license='BSD',
  author='Adam Paszke',
  author_email='apaszke@google.com',
  packages=find_packages(),
  package_data={'dex': ['libDex.so']},
  install_requires=['numpy'],
)
