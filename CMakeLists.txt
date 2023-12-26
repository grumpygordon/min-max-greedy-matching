cmake_minimum_required(VERSION 3.15)
project(proj)

set(CMAKE_CXX_STANDARD 17)

#set(CMAKE_CXX_FLAGS "-DONPC -Wall -Wextra -Wshadow -Wconversion -Wno-sign-compare -Wno-sign-conversion -Wfatal-errors -I ../includes")
set(CMAKE_CXX_FLAGS "-DONPC -Wall -Wextra -Wshadow -Wconversion -Wno-sign-compare -Wno-sign-conversion -Wfatal-errors -Wl,--stack=1000000000 -I ../includes")

set(CMAKE_CXX_FLAGS_RELEASE "-O2")

set(CMAKE_CXX_FLAGS_DEBUG "-g -D_GLIBCXX_DEBUG -D_GLIBCXX_DEBUG_PEDANTIC")
#set(CMAKE_CXX_FLAGS_DEBUG "-g -D_GLIBCXX_DEBUG -D_GLIBCXX_DEBUG_PEDANTIC -fsanitize=address,undefined")
# generators.hpp helpers.hpp propositions.hpp paths.hpp classic.h
add_executable(proj main.cpp)