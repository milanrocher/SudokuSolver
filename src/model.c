#include <stdio.h>
#include "model.h"
#include "sudoku.h"

int main(int argc, char *argv[]) {
    Sudoku sudoku;
    int i, j;

    for (i = 0; i < 9; ++i) {
        for (j = 0; j < 9; ++j) {
            __CPROVER_assume(sudoku.puzzle[i][j] >= 0 && sudoku.puzzle[i][j] <= 9);
        }
    }

    return 0;
}