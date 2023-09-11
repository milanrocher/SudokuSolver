#include <stdio.h>
#include "wrapper.h"
#include "sudoku.h"

int main(int argc, char *argv[]) {
    Sudoku sudoku;

    if (argc != 2) {
        fprintf(stderr, "Usage: %s <input_file>\n", argv[0]);
        return 1;
    }

    if (readSudoku(argv[1], sudoku.puzzle) == 1) {
        fprintf(stderr, "Error loading sudoku.");
    }

    if (runCBMC() == 0) {
        printSudoku(sudoku.puzzle);
    } else {
        printf("UNSOLVABLE");
    }

    return 0;
}

int runCBMC() {
    return 0;
}

int readSudoku(char *fileName, int puzzle[9][9]) {
    int i, j;
    FILE *inputFile;

    inputFile = fopen(fileName, "r");
    if (!inputFile) {
        return 1;
    }

    for (i = 0; i < 9; ++i) {
        for (j = 0; j < 9; ++j) {
            if (!fscanf(inputFile, "%d", &puzzle[i][j])) {
                fclose(inputFile);
                return 1;
            }
        }
    }

    fclose(inputFile);

    return 0;
}

void printSudoku(int puzzle[9][9]) {
    int i, j;

    for (i = 0; i < 9; ++i) {
        for (j = 0; j < 9; ++j) {
            printf("%d ", puzzle[i][j]);
        }
        printf("\n");
    }
}