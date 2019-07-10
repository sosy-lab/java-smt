%module cmakeswig_foobar

%include "std_string.i"
// Add necessary symbols to generated header
%{
#include <foobar/FooBar.hpp>
%}

%ignore "";
namespace foobar {
// Process symbols in header
%rename(run) FooBar::operator();
%include "foobar/FooBar.hpp"
} // namespace foobar
