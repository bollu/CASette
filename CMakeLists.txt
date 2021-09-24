cmake_minimum_required(VERSION 3.20)
project(ward C CXX)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fdiagnostics-color=always -O2")
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -O0 -g -fdiagnostics-color=always -fsanitize=address,undefined")
include_directories(./)

add_executable(tableaux tableaux.cpp)
add_executable(ftsp ftsp.cpp) 
add_executable(cox-division cox-division.cpp) 
install(TARGETS tableaux ftsp DESTINATION bin)

