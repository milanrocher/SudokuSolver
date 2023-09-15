#ifndef BMC_WRAPPER_H
#define BMC_WRAPPER_H

int readSudoku(char *fileName, int sudoku[81]);
int createModel(int sudoku[81]);
void runCBMC();
void printSudoku();

#endif
