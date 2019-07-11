%module foobarapi

%{
  #include "FooBar.hpp"
%}

%include "std_string.i"

/*
%pragma(java) jniclassimports=%{
import foobar.*;
%}

%pragma(java) moduleimports=%{
import foobar.*;
%}
*/

//%nspace foobar::FooBar
%include FooBar.hpp
