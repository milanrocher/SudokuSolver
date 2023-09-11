#ifndef BMC_WRAPPER_H
#define BMC_WRAPPER_H

#include "sudoku.h"

int runCBMC();

int readSudoku(char *fileName, int puzzle[9][9]);

void printSudoku(int puzzle[9][9]);

#endif
