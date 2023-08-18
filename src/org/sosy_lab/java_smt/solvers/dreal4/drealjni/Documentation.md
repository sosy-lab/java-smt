<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

## Documentation:
### How to build the library:
1. First install dReal to get the Library:
   ```
   # Ubuntu 22.04
    sudo apt-get install curl
    curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/ubuntu/22.04/install.sh | sudo bash
   ```
2. Get all the dependencies for dReal. Use the install_prereq.sh script. 
3. Compile dreal_wrap.cxx with:
    ```
    c++ -fpic -c dreal_wrap.cxx -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/ -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/linux -I/opt/dreal/4.21.06.2/include -I/opt/libibex/2.7.4/include -I/opt/libibex/2.7.4/include/ibex -I/opt/libibex/2.7.4/include/ibex/3rd -I/usr/include/coin -L/opt/dreal/4.21.06.2/lib -L/opt/libibex/2.7.4/lib -L/usr/lib/x86_64-linux-gnu -L/usr/lib -ldreal -libex -lClpSolver -lClp -lCoinUtils -lbz2 -lz -llapack -lblas -lm -lnlopt
   ``` 
4. Create shared library with:
    ```
    c++ -shared dreal_wrap.o -L/opt/dreal/4.21.06.2/lib -L/opt/libibex/2.7.4/lib -L/usr/lib/x86_64-linux-gnu -L/usr/lib -ldreal -libex -lClpSolver -lClp -lCoinUtils -lbz2 -lz -llapack -lblas -lm -lnlopt -o libdreal4.so
   ```
   


#### SWIG:
- create SWIG interface (file with .i) and put functions and header in that file
- It is possible to overload ooperators in C++, therefore, it is possible to tell swig to rename the overloaded operators, so that those can be translated to java as well. For that use the ```rename``` command.
- There are a lot of overloads in dReal, especially in the symbolic.h file and the includes of the file. Those overloaded methods need to be handled with rename.
- The interface-file also needs a few includes for handeling specific C++ class templates:
    ```
    %include "std_string.i"
    %include "std_vector.i"
    %include "std_unordered_map.i"
    %include "std_pair.i"
    %include "std_shared_ptr.i"
    %include "std_set.i"
    %include "std_map.i"
    ```
- To use std::set and so on, you need to specify how the template is going to be named, so to wrapp std::set with a certain type, it needs to be specified, for example:
    ```
    std::set<Formula> ->
    %template(<name>) std::set<Formula> 
    ```
    So SWIG knows how to name the generated class.
- In C++ templates can be used. A template is a construct that generates an ordinary type or function at compile time based on arguments the user supplies for the template parameters.
In order to use that, the templates must be wrapped with a type, to do so, in the interface file the template needs to be defined and wraped like:
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
    Use the following commands (be careful with dependecies!!!):
    - C++:
        ```bash
        # General usage
        c++ -fpic -c <file_name>_wrap.cxx -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/ -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/linux  
        
        # This is specific for dReal, so that all the right dependecies are included
        c++ -fpic -c dreal_wrap.cxx -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/ -I/usr/lib/jvm/java-1.11.0-openjdk-amd64/include/linux -I/opt/dreal/4.21.06.2/include -I/opt/libibex/2.7.4/include -I/opt/libibex/2.7.4/include/ibex -I/opt/libibex/2.7.4/include/ibex/3rd -I/usr/include/coin -L/opt/dreal/4.21.06.2/lib -L/opt/libibex/2.7.4/lib -L/usr/lib/x86_64-linux-gnu -L/usr/lib -ldreal -libex -lClpSolver -lClp -lCoinUtils -lbz2 -lz -llapack -lblas -lm -lnlopt
        ```

        For the libaries to work, the dependencies of ibex and dreal are needed. Therefore, the library is compiled with those two libraries, which should be both in the same directory:
        ```bash
        # General usage
        c++ -shared <file_name>_wrap.o -o <file_name_of_shared_lib>.so
      
        # This is specific for dReal, so that all the right dependecies are included
        c++ -shared dreal_wrap.o -L/opt/dreal/4.21.06.2/lib -L/opt/libibex/2.7.4/lib -L/usr/lib/x86_64-linux-gnu -L/usr/lib -ldreal -libex -lClpSolver -lClp -lCoinUtils -lbz2 -lz -llapack -lblas -lm -lnlopt -o libdreal4.so

        ```
- Compile the java files example.java and main.java to create the class files example.class and main.class before running main in the JVM. Ensure that the libexample.so file is in your LD_LIBRARY_PATH before running. For example: 
    ```bash
    export LD_LIBRARY_PATH=. 
    javac *.java
    java main
    ```

### General remarks SWIG:
- std::ostream  is with SWIGTYPE generated, no solution yet, but maybe ok because only for output

### SWIG File remarks:
#### Config File:
- std::function not supported, work around?
    - therefore Brancher does not work and dynamicBitset does not work  
    - Because dynamicBitset not used in Conifg file, class not wraped
- OptionValue satDefault not possible, but should be possible if done by hand with the templates of OptionValue Int etc. (doch möglich da ja im template die klasse definiert wird?)
- mutable function not working, need to be implemented as well and looked at how they work

#### API File:
- optional not supported, but api has for checkSatisfiability the option to use the boolean method (same for the other method)

#### Context File:
- ScopedVector not working
- optional not supported, need to look for workaround 
- both ignored for now
- Class not needed?

#### Symbolic File:
- hash.h? hash_value never used?
- std::function not supported

##### Environment File:
- std::unordered_map does not work
    - begin(), end() etc. do not work, problem in Variables as well
- Indexing has SWIGTYPE_p_double should be double -> per Hand
- Uses intitializer_list, but not supported -> work around like in Variables?

##### Expression File.
- ExpressionSubstitution & FormulaSubstitution do not work 
    - template for std::unordered_map return error: not more than 2 templates oder sowas
- Same in Formula

##### Variables File:
- std::unordered_map does not work 
    - begin(), end() etc. do not work
    - it is just a set, so maybe work around possible if self written

##### Formula File:
- weird error, make_conjunction() and make_disjunction() duplicates, but there are not -> do it myself

#### OptionValue Class:
- AssignOperator has type SWIGTYPE, can be change to write type by hand

#### Ibex:
- Ibex ignored, therefore SWIGTYPE generated, maybe does work as well
- Ibex not wrapped, because lib did not work, so trying to avoid to generate ibex


### Changes made to the following files:
#### symbolic_formula.h
- in line 160: ```bool Evaluate(const Environment& env = Environment{}) const;``` zu ```bool Evaluate(const Environment& env = Environment()) const; ``` -> vllt durch c++ 11 auch gelöst?   
- in line 291: Line commented
- in line 313: Line commented
    - or this Error:
        ```
        dreal/symbolic/symbolic.h:119: Error: 'make_conjunction' is multiply defined in the generated target language module in scope 'dreal_SymbolicJNI'.
        /home/julius/Desktop/dreal4/dreal/symbolic/symbolic_formula.h:291: Error: Previous declaration of 'make_conjunction'
        dreal/symbolic/symbolic.h:124: Error: 'make_disjunction' is multiply defined in the generated target language module in scope 'dreal_SymbolicJNI'.
        /home/julius/Desktop/dreal4/dreal/symbolic/symbolic_formula.h:313: Error: Previous declaration of 'make_disjunction'
        ```
        -> selber einfügen?
#### symbolic_expression.h
- line 234: ```double Evaluate(const Environment& env = Environment{}) const;``` zu ```double Evaluate(const Environment& env = Environment()) const; ```



### Compiling!!
```bash
c++ Test.cc -o Test.out -I/opt/dreal/4.21.06.2/include -I/opt/libibex/2.7.4/include -I/opt/libibex/2.7.4/include/ibex -I/opt/libibex/2.7.4/include/ibex/3rd -I/usr/include/coin -L/opt/dreal/4.21.06.2/lib -L/opt/libibex/2.7.4/lib -L/usr/lib/x86_64-linux-gnu -L/usr/lib -ldreal -libex -lClpSolver -lClp -lCoinUtils -lbz2 -lz -llapack -lblas -lm -lnlopt
    
```

### Was nicht funktioniert:
#### Expression:
- EvaluatePartial not tested 
- Substitute funktioniert nur mit Variable und Expression
- get_first/second_argument bekommt man Expression, aber kann nicht z.b auf gleichheit testen, aber in c++ auch so
- Nicht alle statitschen methoden getestet, aber alles funktioniert sonst, also sollte auch alles gehen 

#### Variables:
- begin(), end() ..., find() usw geht nicht

#### Environment:
- der eine Konstruktor mit intializer_list geht nicht, mit initializer_list<Variable> selber konstruiert
- begin(), end(), ..., find() usw. geht nicht, wie bei Variables

#### Formula:
- Substitute geht nicht mit ExpressionSubstitution, FormulaSubstitution
- Substitute mit Formula, läuft durch aber ändert nichts, aber auch in C++ nicht, wie funktioniert die Funktion?
- make_conjunction/dijunction selber machen? in symbolic die selbe nur mit vector? ALso egal ob mit vector erstelle oder mit set??
- Überladenden operatoren nicht getestet, da indirekt getestet durch anlegen von Formulas .... -> nicht so gut
- get_variable ?, Formula get_operands, mit set gehts, bzw. wirft kein Fehler ?, get_quantified_formula ?

#### Symbolic:
- map funktioniert nicht, da std::function nicht unterstützt ist
- DeltaWeaken/Strengthen, IsDifferentiable? Was tun die Funktionen? Daher nur geguckt ob die keinen Fehler werfen

#### Context:
- nicht getestet, da nur durch api verwendet wird, d.h. CheckSatisfiability() verwendet context nur intern, 
Klasse überflüssig?
- Wenn Context gebraucht wird, CheckSat Rückgabe wert vorher überprüfen und wie bei API machen mit übergabe

#### Config:
- Brancher geht nicht
- dump_theory_literals findet er die dependecy nicht?
- Default Brancher gesetzt, aber nicht änderbar, da ich nicht weiß, welche Möglichkeiten es gibt, daher nur default.
- SatDefaultPhase kann man nicht ändern, erstmal weggelassen
### Was noch angeguckt werden muss:
#### Box:
- Interval, IntervalVector gehen nicht, aber wichtig um Lösung auszugeben?
- Wenn nur LÖsung ausgeben dann einfach printen die Box? 
- set_empty() komisches verhalten? Aber ist genauso in dreal
- InplaceUnion nur getestet ob durch läuft, was tut das?

#### API:
- Minimize mit Config stürtz ab



