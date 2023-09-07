cmake_minimum_required(VERSION 3.26)
project(bmc C)

set(CMAKE_C_STANDARD 11)

include_directories(.)

add_executable(bmc
        src/sudoku.c
        src/sudoku.h
        src/wrapper.c
        src/wrapper.h)
