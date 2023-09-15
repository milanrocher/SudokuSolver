#ifndef BMC_WRAPPER_H
#define BMC_WRAPPER_H

int readSudoku(char *fileName, int sudoku[81]);
int printSudoku();
int createModel(int sudoku[81]);
void runCBMC();
unsigned long hashArray(int arr[]);

#endif
