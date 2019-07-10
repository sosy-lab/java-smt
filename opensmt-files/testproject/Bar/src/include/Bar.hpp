#pragma once

#include <string>

//! @namespace bar The Bar namespace
namespace bar {
//! @brief Free function in bar namespace.
//! @param[in] level Scope level.
std::string barHello(int level);

//! @brief Class Bar.
class Bar {
 public:
  //! @brief Static method of Bar class.
  //! @param[in] level Scope level.
  static std::string hello(int level);

  std::string operator()() const;
};
}  // namespace bar
