#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "wrapper.h"

#define INDEX(row, col) ((row) * 9 + (col))

int silentMode = 0;

int main(int argc, char *argv[]) {
  int sudoku[81];

  if (argc != 3 && argc != 4) {
    fprintf(stderr, "Usage: %s --<mode> [--silent] <input_file>\n", argv[0]);
    return 1;
  }

  if (argc == 4 && strcmp(argv[2], "--silent") == 0) {
    silentMode = 1;
  }

  if (readSudoku(argv[argc - 1], sudoku) == 1) {
    fprintf(stderr, "Error loading sudoku.\n");
    return 1;
  }

  if (createModel(sudoku) == 1) {
    fprintf(stderr, "Error creating model file.\n");
    return 1;
  }

  struct timespec start, end;
  clock_gettime(CLOCK_MONOTONIC, &start);

  if (strcmp(argv[1], "--basic") == 0) {
    runCBMC();
    if (printSudoku() == 1) {
      printf("UNSOLVABLE\n");
    }
  } else if (strcmp(argv[1], "--exhaustive") == 0) {
    int solutionCount = 0;

    while (1) {
      runCBMC();
      printSudoku();

      // TODO
      solutionCount++;
    }

    // Print the total number of solutions
    printf("NUMBER OF SOLUTIONS: %d\n", solutionCount);
  }

  clock_gettime(CLOCK_MONOTONIC, &end);
  double time_taken = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
  printf("Elapsed Time: %.9f seconds\n", time_taken);

  return 0;
}

int readSudoku(char *fileName, int sudoku[81]) {
  FILE *inputFile = fopen(fileName, "r");
  if (!inputFile) {
    return 1;
  }

  for (int i = 0; i < 81; ++i) {
    if (!fscanf(inputFile, "%d", &sudoku[i])) {
      fclose(inputFile);
      return 1;
    }
  }

  fclose(inputFile);

  return 0;
}

int createModel(int sudoku[81]) {
  FILE *outputFile = fopen("model.c", "w");
  if (!outputFile) {
    return 1;
  }

  fprintf(outputFile, "#include <stdio.h>\n");
  fprintf(outputFile, "#include <stdint.h>\n\n");

  fprintf(outputFile, "#define INDEX(row, col) ((row) * 9 + (col))\n\n");

  fprintf(outputFile, "int main(int argc, char *argv[]) {\n");
  fprintf(outputFile, "  /*\n   * Sudoku structure.\n   */\n");
  fprintf(outputFile, "  int sudoku[81] = {\n");

  for (int i = 0; i < 9; i++) {
    fprintf(outputFile, "      ");
    for (int j = 0; j < 9; j++) {
      fprintf(outputFile, "%d", sudoku[INDEX(i, j)]);
      if (j < 8) {
        fprintf(outputFile, ", ");
      }
    }
    fprintf(outputFile, ",\n");
  }
  fprintf(outputFile, "  };\n\n");

  fprintf(outputFile, "  /*\n   * Create nondeterministic search space for empty cells.\n   */\n");
  fprintf(outputFile, "  for (int i = 0; i < 9; ++i) {\n");
  fprintf(outputFile, "    for (int j = 0; j < 9; ++j) {\n");
  fprintf(outputFile, "      if (sudoku[INDEX(i, j)] == 0) {\n");
  fprintf(outputFile, "        int cell = nondet_int();\n");
  fprintf(outputFile, "        __CPROVER_assume(cell >= 1 && cell <= 9);\n");
  fprintf(outputFile, "        sudoku[INDEX(i, j)] = cell;\n");
  fprintf(outputFile, "      }\n");
  fprintf(outputFile, "    }\n");
  fprintf(outputFile, "  }\n\n");

  fprintf(outputFile, "  /*\n   * Bit maks for uniqueness\n   */\n");
  fprintf(outputFile, "  uint16_t rows[9] = {0};\n");
  fprintf(outputFile, "  uint16_t cols[9] = {0};\n");
  fprintf(outputFile, "  uint16_t blocks[9] = {0};\n\n");

  fprintf(outputFile, "  for (int i = 0; i < 9; i++) {\n");
  fprintf(outputFile, "    for (int j = 0; j < 9; j++) {\n");
  fprintf(outputFile, "      int val = sudoku[INDEX(i, j)];\n");
  fprintf(outputFile, "      int bit = 1 << (val - 1);\n\n");

  fprintf(outputFile, "      /*\n");
  fprintf(outputFile, "       * Each number appears at most once in each row.\n");
  fprintf(outputFile, "       */\n");
  fprintf(outputFile, "      __CPROVER_assume(!(rows[i] & bit));\n");
  fprintf(outputFile, "      /*\n");
  fprintf(outputFile, "       * Each number appears at most once in each col.\n");
  fprintf(outputFile, "       */\n");
  fprintf(outputFile, "      __CPROVER_assume(!(cols[j] & bit));\n");
  fprintf(outputFile, "      /*\n");
  fprintf(outputFile, "       * Each number appears at most once in each block.\n");
  fprintf(outputFile, "       */\n");
  fprintf(outputFile, "      __CPROVER_assume(!(blocks[(i / 3) * 3 + j / 3] & bit));\n\n");
  fprintf(outputFile, "      /*\n");
  fprintf(outputFile, "       * Set as seen.\n");
  fprintf(outputFile, "       */\n");
  fprintf(outputFile, "      rows[i] |= bit;\n");
  fprintf(outputFile, "      cols[j] |= bit;\n");
  fprintf(outputFile, "      blocks[(i / 3) * 3 + j / 3] |= bit;\n");
  fprintf(outputFile, "    }\n");
  fprintf(outputFile, "  }\n\n");

  fprintf(outputFile, "  /*\n   * Start search.\n   */\n");
  fprintf(outputFile, "  assert(0);\n\n");

  fprintf(outputFile, "  return 0;\n");
  fprintf(outputFile, "}\n");

  fclose(outputFile);

  return 0;
}

void runCBMC() {
  system("/home/milan/.repos/cbmc-cbmc-5.90.0/src/cbmc/cbmc --trace model.c | grep -o 'val=[0-9]\\+' | cut -d '=' -f 2 > output.txt");
}

int printSudoku() {
  FILE *inputFile = fopen("output.txt", "r");
  if (!inputFile) {
    return 1;
  }

  for (int i = 0; i < 9; i++) {
    for (int j = 0; j < 9; j++) {
      int num;
      if (fscanf(inputFile, "%d", &num) != 1) {
        fclose(inputFile);
        return 1;
      }
      printf("%d", num);
      if (j < 8) {
        printf(" ");
      }
    }
    printf("\n");
  }

  fclose(inputFile);
  return 0;
}

unsigned long hashArray(int arr[]) {
  unsigned long hash = 0;
  for (int i = 0; i < 81; i++) {
    hash = (hash * 37) + arr[i];
  }
  return hash;
}