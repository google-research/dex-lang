from setuptools import setup, find_packages

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
  
