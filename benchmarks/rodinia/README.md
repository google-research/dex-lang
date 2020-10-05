# Dex implementation of the Rodinia benchmark suite

Implementation of each benchmark can be found in the `XYZ.dx` file in this directory.
They don't contain any IO code, so running them will only type-check the definitions.
All runnable scripts are generated in the process of running `python prepare-executables.py`.
Note that the Python script assumes that you have the Rodinia suite downloaded and placed in the `rodinia/` subdirectory of this one.
The original benchmark suite is necessary to retrieve the standard example inputs.
