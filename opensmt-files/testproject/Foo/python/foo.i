%module pyFoo

%include "std_string.i"
// Add necessary symbols to generated header
%{
#include <foo/Foo.hpp>
%}

// Process symbols in header
%include "foo/Foo.hpp"
