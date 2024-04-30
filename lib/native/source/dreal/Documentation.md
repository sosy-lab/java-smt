<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

## Documentation:
### Building on Ubuntu 23.10
0. Get the source from github
1. Install Bazel from the github release
`https://github.com/bazelbuild/bazel/releases/download/7.1.1/bazel_7.1.1-linux-x86_64.deb`
2. Get libibex from the ppa
`https://launchpad.net/~dreal/+archive/ubuntu/dreal/+sourcepub/13805166/+listing-archive-extra`
3. Install missing dependencies with apt
```
bison
coinor-libclp-dev
g++
libfl-dev
libgmp-dev
libibex-dev
libnlopt-cxx-dev
libpython3-dev
pkg-config
python3-distutils
python3-minimal
zlib1g-dev
```
4. Build with bazel
`bazel build //...`
5. Comment out the broken test
6. Run bazel again
7. Library can be found in `bazel-bin/libdreal_.so`. Run `bazel build //:package_debian` to 
   generate a deb package and install it.
8. Compile the SIWG wrapper with `g++ -fpic -c dreal_wrap.cxx -I/usr/lib/jvm/java-20-openjdk-amd64/include/ -I/usr/lib/jvm/java-20-openjdk-amd64/include/linux -I/opt/libibex/2.7.4/include/ -I/opt/libibex/2.7.4/include/ibex -I/opt/libibex/2.7.4/include/ibex/3rd -I/opt/dreal/4.21.06.2/include/`
9. Then link it with `g++ -shared dreal_wrap.o -L/opt/libibex/2.7.4/lib -L/opt/dreal/4.21.06.2/lib 
   -ldreal_ -libex -o libdrealjava.so`
10. Patch with rpath

### How to build the library:
1. Install the dependencies for libibex-dev
    ```bash
    sudo apt-get update && apt install -y software-properties-common
    ```
2. Install git, curl, g++, java. Curl is used, because dReal will be installed and in the 
   directory dreal, all the header files can be found. In the directory symbolic, for example,
   will be every header file, that is used in the wrapper. If dReal is just cloned, the header 
   files will not be in the directory dreal/symbolic, they will be in the directory 
   third_party/com_github_robotlocomotion_drake/dreal/symbolic. For the wrapper it is easier to 
   just import the dreal/dreal.h file with all the necassary header files and use the installed 
   version of dReal, because C++ will find all the header files at one place.
    ```bash
   sudo apt update && apt install -y git -y curl  -y g++ -y openjdk-11-jdk
    ```
3. Install dReal and dependencies
    ```bash
   sudo curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/ubuntu/22.04/install.
   sh | bash
   ```
4. Move the shared libraries into the system folder. Otherwise, when creating the shared library 
   for the JNI, it will not find libibex.so or libdreal.so.
    ```bash
   sudo cp /opt/dreal/4.21.06.2/lib/libdreal.so /usr/lib/ &&
   sudo cp /opt/libibex/2.7.4/lib/libibex.so /usr/lib/
   ```
5. Compile the wrapper file and create the shared library
    ```
   c++ -fpic -c dreal_wrap.cxx -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/ -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/linux -I/opt/dreal/4.21.06.2/include -I/opt/libibex/2.7.4/include -I/opt/libibex/2.7.4/include/ibex -I/opt/libibex/2.7.4/include/ibex/3rd -I/usr/include/coin -L/opt/dreal/4.21.06.2/lib -L/opt/libibex/2.7.4/lib -L/usr/lib/x86_64-linux-gnu -L/usr/lib -ldreal -libex -lClpSolver -lClp -lCoinUtils -lbz2 -lz -llapack -lblas -lm -lnlopt
   c++ -shared dreal_wrap.o -L/opt/dreal/4.21.06.2/lib -L/opt/libibex/2.7.4/lib -L/usr/lib/x86_64-linux-gnu -L/usr/lib -ldreal -libex -lClpSolver -lClp -lCoinUtils -lbz2 -lz -llapack -lblas -lm -lnlopt -o libdreal4.so
   ```

### SWIG:
It is also possible to generate new JNI code. For that a SWIG interface needs to be created and 
functions and headers need to be in that file, that should be translated.
#### Example for dReal:
- create SWIG interface (file with .i) and put functions and header in that file
- It is possible to overload operators in C++, therefore, it is possible to tell swig to rename the overloaded operators, so that those can be translated to java as well. For that use the ```rename``` command.
- There are a lot of overloads in dReal, especially in the symbolic.h file and the includes of the file. Those overloaded methods need to be handled with rename.
- The interface-file also needs a few includes for handling specific C++ class templates if the 
  translated code uses them:
    ```
    %include "std_string.i"
    %include "std_vector.i"
    %include "std_unordered_map.i"
    %include "std_pair.i"
    %include "std_shared_ptr.i"
    %include "std_set.i"
    %include "std_map.i"
    ```
- To use std::set and so on, you need to specify how the template is going to be named, so to wrap std::set with a certain type, it needs to be specified, for example:
    ```
    std::set<Formula> ->
    %template(<name>) std::set<Formula> 
    ```
    So SWIG knows how to name the generated class.
- In C++ templates can be used. A template is a construct that generates an ordinary type or function at compile time based on arguments the user supplies for the template parameters.
In order to use that, the templates must be wrapped with a type, to do so, in the interface file the template needs to be defined and wrapped like:
    ```
    namespace dreal {
    template <typename T>
    class OptionValue {
    public:
    enum class Type {
        DEFAULT,            ///< Default value
        FROM_FILE,          ///< Updated by a set-option/set-info in a file
        FROM_COMMAND_LINE,  ///< Updated by a command-line argument
        FROM_CODE,          ///< Explicitly updated by a code
    };

    /// Constructs an option value with @p value.
    explicit OptionValue(T value)
        : value_{std::move(value)}, type_{Type::DEFAULT} {}

    /// Default copy constructor.
    OptionValue(const OptionValue&) = default;

    /// Default move constructor.
    OptionValue(OptionValue&&) noexcept = default;

    /// Default copy assign operator.
    OptionValue& operator=(const OptionValue&) = default;

    /// Default move assign operator.
    OptionValue& operator=(OptionValue&&) noexcept = default;

    /// Default destructor.
    ~OptionValue() = default;

    /// Copy-assign operator for T.
    ///
    /// Note: It sets value with `Type::FROM_CODE` type.
    OptionValue& operator=(const T& value) {
        value_ = value;
        type_ = Type::FROM_CODE;
        return *this;
    }

    /// Move-assign operator for T.
    ///
    /// Note: It sets value with `Type::FROM_CODE` type.
    OptionValue& operator=(T&& value) {
        value_ = std::move(value);
        type_ = Type::FROM_CODE;
        return *this;
    }

    /// Returns the value.
    const T& get() const { return value_; }

    /// Sets the value to @p value which is given by a command-line argument.
    void set_from_command_line(const T& value) {
        if (type_ != Type::FROM_CODE) {
        value_ = value;
        type_ = Type::FROM_COMMAND_LINE;
        }
    }

    /// Sets the value to @p value which is provided from a file.
    ///
    /// @note This operation is ignored if the current value is set by
    /// command-line.
    void set_from_file(const T& value) {
        switch (type_) {
        case Type::DEFAULT:
        case Type::FROM_FILE:
            value_ = value;
            type_ = Type::FROM_FILE;
            return;

        case Type::FROM_COMMAND_LINE:
        case Type::FROM_CODE:
            // No operation.
            return;
        }
    }

    friend std::ostream& operator<<(std::ostream& os, Type type) {
        switch (type) {
        case OptionValue<T>::Type::DEFAULT:
            return os << "DEFAULT";
        case OptionValue<T>::Type::FROM_FILE:
            return os << "FROM_FILE";
        case OptionValue<T>::Type::FROM_COMMAND_LINE:
            return os << "FROM_COMMAND_LINE";
        case OptionValue<T>::Type::FROM_CODE:
            return os << "FROM_CODE";
        }
    }

    private:
    T value_;
    Type type_;
    };

    %template(OptionValueBool) OptionValue<bool>;
    %template(OptionValueInt) OptionValue<int>;
    %template(OptionValueDouble) OptionValue<double>;
    %template(OptionValueUnsignedInt) OptionValue<uint32_t>;
    }
    ```

- The order of the includes is important, so that a class that is used in different headers must be wraped first, so it is known to SWIG in other files
- To create a wrapper file with SWIG use the following command :
    - C++ 
        ```bash
        swig -c++ -java <filename>.i 
        ``` 
- Compile <file_name>_wrap.cxx to create the extension lib.so (unix). In order to compile the C++ wrappers, the compiler needs the jni.h and jni_md.h header files which are part of the JDK. They are usually in directories like this:
    ```bash
    /usr/java/include
    /usr/java/include/<operating_system>
    ```
    Use the following commands (be careful with dependencies):
    - C++:
        ```bash
        # General usage
        c++ -fpic -c <file_name>_wrap.cxx -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/ -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/linux  
        
        # This is specific for dReal, so that all the right dependencies are included
        c++ -fpic -c dreal_wrap.cxx -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/ -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/linux -I/opt/dreal/4.21.06.2/include -I/opt/libibex/2.7.4/include -I/opt/libibex/2.7.4/include/ibex -I/opt/libibex/2.7.4/include/ibex/3rd -I/usr/include/coin -L/opt/dreal/4.21.06.2/lib -L/opt/libibex/2.7.4/lib -L/usr/lib/x86_64-linux-gnu -L/usr/lib -ldreal -libex -lClpSolver -lClp -lCoinUtils -lbz2 -lz -llapack -lblas -lm -lnlopt
        ```

        For the libaries to work, the dependencies of ibex and dreal are needed. Therefore, the library is compiled with those two libraries, which should be both in the same directory:
        ```bash
        # General usage
        c++ -shared <file_name>_wrap.o -o <file_name_of_shared_lib>.so
      
        # This is specific for dReal, so that all the right dependencies are included
        c++ -shared dreal_wrap.o -L/opt/dreal/4.21.06.2/lib -L/opt/libibex/2.7.4/lib -L/usr/lib/x86_64-linux-gnu -L/usr/lib -ldreal -libex -lClpSolver -lClp -lCoinUtils -lbz2 -lz -llapack -lblas -lm -lnlopt -o libdreal4.so

        ```




