#pragma once

#include <string>

//! @namespace foobar The Foobar namespace.
namespace foobar {
//! @brief Free function in foobar namespace
//! @param[in] level Scope level.
std::string foobarHello(int level);

//! @brief Class FooBar.
class FooBar {
 public:
  //! @brief Static method of FooBar class.
  //! @param[in] level Scope level.
  static std::string hello(int level);
  
  std::string welcome(){ return "Sie sind Willkommen !!!";}
  std::string operator()() const;
};
}  // namespace foobar
