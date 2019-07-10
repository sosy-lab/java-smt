#include "include/Foo.hpp"
#include <sstream>
#include <iostream>
//#include <string>

namespace foo {
std::string fooHello(int level) {
  std::stringstream buffer; 

  buffer << "[" << level << "] Enter fooHello" << std::endl;
  buffer << "[" << level << "] Exit fooHello" << std::endl;

  return buffer.str();
}

std::string Foo::hello(int level) {
  std::stringstream buffer; 

  buffer << "[" << level << "] Enter Foo::hello" << std::endl;
  foo::fooHello(level + 1);
  buffer << "[" << level << "] Exit Foo::hello" << std::endl;

  return buffer.str();
}

std::string Foo::operator()() const { return "Foo"; }
}  // namespace foo
