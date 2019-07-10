%module pyFooBar

%include "std_string.i"
// Add necessary symbols to generated header
%{
#include <foobar/FooBar.hpp>
%}

// Process symbols in header
%include "foobar/FooBar.hpp"
