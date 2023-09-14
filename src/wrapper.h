#ifndef BMC_WRAPPER_H
#define BMC_WRAPPER_H

int readSudoku(char *fileName, int sudoku[9][9]);
int createModel(int sudoku[9][9]);
void runCBMC();
void printSudoku();

#endif
