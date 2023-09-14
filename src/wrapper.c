#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "wrapper.h"

int main(int argc, char *argv[]) {
  int sudoku[9][9];

  if (argc != 2) {
    fprintf(stderr, "Usage: %s <input_file>\n", argv[0]);
    return 1;
  }

  if (readSudoku(argv[1], sudoku) == 1) {
    fprintf(stderr, "Error loading sudoku.\n");
  }

  if (createModel(sudoku) == 1) {
    fprintf(stderr, "Error creating model file.\n");
  }

  struct timespec start, end;
  clock_gettime(CLOCK_MONOTONIC, &start);

  runCBMC();
  printSudoku();

  clock_gettime(CLOCK_MONOTONIC, &end);
  double time_taken = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
  printf("Elapsed Time: %f seconds\n", time_taken);

  return 0;
}

int readSudoku(char *fileName, int sudoku[9][9]) {
  FILE *inputFile = fopen(fileName, "r");
  if (!inputFile) {
    return 1;
  }

  for (int i = 0; i < 9; ++i) {
    for (int j = 0; j < 9; ++j) {
      if (!fscanf(inputFile, "%d", &sudoku[i][j])) {
        fclose(inputFile);
        return 1;
      }
    }
  }

  fclose(inputFile);

  return 0;
}

int createModel(int sudoku[9][9]) {
  FILE *outputFile = fopen("model.c", "w");
  if (!outputFile) {
    return 1;
  }

  fprintf(outputFile, "int main(int argc, char *argv[]) {\n");
  fprintf(outputFile, "  int sudoku[9][9] = {\n");

  for (int i = 0; i < 9; i++) {
    fprintf(outputFile, "    {");
    for (int j = 0; j < 9; j++) {
      fprintf(outputFile, "%d", sudoku[i][j]);
      if (j < 8) {
        fprintf(outputFile, ", ");
      }
    }
    fprintf(outputFile, "},\n");
  }
  fprintf(outputFile, "  };\n\n");

  fprintf(outputFile, "  for (int i = 0; i < 9; ++i) {\n");
  fprintf(outputFile, "    for (int j = 0; j < 9; ++j) {\n");
  fprintf(outputFile, "      if (sudoku[i][j] == 0) {\n");
  fprintf(outputFile, "        int cell = nondet_int();\n");
  fprintf(outputFile, "        __CPROVER_assume(cell >= 1 && cell <= 9);\n");
  fprintf(outputFile, "        sudoku[i][j] = cell;\n");
  fprintf(outputFile, "      }\n");
  fprintf(outputFile, "    }\n");
  fprintf(outputFile, "  }\n\n");

  fprintf(outputFile, "  for (int i = 0; i < 9; i++) {\n");
  fprintf(outputFile, "    for (int j = 0; j < 9; j++) {\n");
  fprintf(outputFile, "      int val = sudoku[i][j];\n");
  fprintf(outputFile, "      for (int k = j + 1; k < 9; k++) {\n");
  fprintf(outputFile, "        __CPROVER_assume(sudoku[i][k] != val);\n");
  fprintf(outputFile, "      }\n\n");
  fprintf(outputFile, "      for (int k = i + 1; k < 9; k++) {\n");
  fprintf(outputFile, "        __CPROVER_assume(sudoku[k][j] != val);\n");
  fprintf(outputFile, "      }\n\n");
  fprintf(outputFile, "      int block_row = i / 3 * 3;\n");
  fprintf(outputFile, "      int block_col = j / 3 * 3;\n");
  fprintf(outputFile, "      for (int m = block_row; m < block_row + 3; m++) {\n");
  fprintf(outputFile, "        for (int n = block_col; n < block_col + 3; n++) {\n");
  fprintf(outputFile, "          if (m != i || n != j) {\n");
  fprintf(outputFile, "            __CPROVER_assume(sudoku[m][n] != val);\n");
  fprintf(outputFile, "          }\n");
  fprintf(outputFile, "        }\n");
  fprintf(outputFile, "      }\n");
  fprintf(outputFile, "    }\n");
  fprintf(outputFile, "  }\n\n");

  fprintf(outputFile, "  assert(0);\n\n");

  fprintf(outputFile, "  return 0;\n");
  fprintf(outputFile, "}\n");

  fclose(outputFile);

  return 0;
}

void runCBMC() {
  system("/home/milan/.repos/cbmc-cbmc-5.90.0/src/cbmc/cbmc --trace model.c | grep -o 'val=[0-9]\\+' | cut -d '=' -f 2 > output.txt");
}

void printSudoku() {
  FILE *inputFile = fopen("output.txt", "r");
  if (!inputFile) {
    return;
  }

  for (int i = 0; i < 9; i++) {
    for (int j = 0; j < 9; j++) {
      int num;
      if (fscanf(inputFile, "%d", &num) != 1) {
        fclose(inputFile);
        printf("UNSOLVABLE\n");
        return;
      }
      printf("%d", num);
      if (j < 8) {
        printf(" ");
      }
    }
    printf("\n");
  }

  fclose(inputFile);
}