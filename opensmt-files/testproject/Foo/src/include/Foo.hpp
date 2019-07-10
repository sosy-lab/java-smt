#pragma once

#include <string>

//! @namespace foo The Foo namespace
namespace foo {
//! @brief Free function in foo namespace.
//! @param[in] level Scope level.
std::string fooHello(int level);

//! @brief Class Foo.
class Foo {
 public:
  //! @brief Static method of Foo class.
  //! @param[in] level Scope level.
  static std::string hello(int level);

  std::string operator()() const;
};
}  // namespace foo
