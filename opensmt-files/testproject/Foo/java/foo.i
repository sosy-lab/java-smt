%module cmakeswig_foo

%include "std_string.i"

// Add necessary symbols to generated header
%{
#include <foo/Foo.hpp>
%}

%ignore "";
namespace foo {
// Process symbols in header
%rename(run) Foo::operator();
%include "foo/Foo.hpp"
} // namespace foo
