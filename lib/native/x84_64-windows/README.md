# How to install Z3 for Windows64 for developers of JavaSMT

## Note:

These steps are not required for using JavaSMT as a library,
but only for developing JavaSMT with Z3 support on a Windows machine.

## Instruction:

Windows does not allow user-space symlinks,
but requires administrator rights to create them.
Thus, we cannot check them into the repository.
Please execute the following as administrator:

- mklink libz3.dll ..\..\java\runtime-z3\libz3.dll
- mklink libz3java.dll ..\..\java\runtime-z3\libz3java.dll

An alternative simple solution is to copy over those files
from the `lib\java\runtime-*\` directory into the current directory.
