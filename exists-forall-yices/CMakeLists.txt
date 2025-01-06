cmake_minimum_required(VERSION 3.4.3)
project(tinyfort C CXX)

# Colors when compiling with clang
# set(CMAKE_CXX_FLAGS "-fdiagnostics-color=always -fno-rtti -g -Wall -Werror")
# set(CMAKE_CXX_FLAGS "-fdiagnostics-color=always -O0 -g -Wall")

find_library(Z3 REQUIRED)
add_executable(solver solver.cpp)

target_link_libraries(solver ${Z3_LIBS})
set_target_properties(solver PROPERTIES CXX_STANDARD 14)
