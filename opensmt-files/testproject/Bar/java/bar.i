%module cmakeswig_bar

%include "std_string.i"
// Add necessary symbols to generated header
%{
#include <bar/Bar.hpp>
%}

%ignore "";
namespace bar {
// Process symbols in header
%rename(run) Bar::operator();
%include "bar/Bar.hpp"
} // namespace bar
