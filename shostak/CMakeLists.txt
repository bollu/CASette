cmake_minimum_required(VERSION 3.4.3)
project(shostak C CXX)

find_library(Z3 REQUIRED)
add_executable(solver solver.cpp)

target_link_libraries(solver ${Z3_LIBS})
set_target_properties(solver PROPERTIES CXX_STANDARD 20)
