#include "../include/Bar.hpp"
#include <sstream>
#include <iostream>

namespace bar {
std::string barHello(int level) {
  std::stringstream buffer;

  buffer << "[" << level << "] Enter barHello" << std::endl;
  buffer << "[" << level << "] Exit barHello" << std::endl;
  return buffer.str();
}

std::string Bar::hello(int level) {
  std::stringstream buffer;

  buffer << "[" << level << "] Enter Bar::hello" << std::endl;
  bar::barHello(level + 1);
  buffer << "[" << level << "] Exit Bar::hello" << std::endl;

  return buffer.str();
}

std::string Bar::operator()() const { return "Bar"; }
}  // namespace bar
