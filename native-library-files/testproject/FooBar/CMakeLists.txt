cmake_minimum_required(VERSION 3.8.0)

project(foobar)

add_library(foobar SHARED ./src/FooBar.cpp ./include/FooBar.hpp
                          ../Bar/src/Bar.cpp ../Bar/include/Bar.hpp
                          ../Foo/src/Foo.cpp ../Foo/include/Foo.hpp
)
