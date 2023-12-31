#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "wrapper.h"

#define INDEX(row, col) ((row) * 9 + (col))
#define MAXSOLUTIONS 100

int silentMode = 0;
int mode = 0;

int main(int argc, char *argv[]) {
  int sudoku[81];

  if (argc != 3 && argc != 4) {
    fprintf(stderr, "Usage: %s --<mode> [--silent] <input_file>\n", argv[0]);
    return 1;
  }

  /* Set execution mode. */
  if (strcmp(argv[1], "--basic") == 0) {
    mode = 0;
  } else if (strcmp(argv[1], "--exhaustive") == 0) {
    mode = 1;
  }
  if (mode == 1 && argc == 4 && strcmp(argv[2], "--silent") == 0) {
    silentMode = 1;
  }

  /* Read Sudoku puzzle from input. */
  if (readSudoku(argv[argc - 1], sudoku) == 1) {
    fprintf(stderr, "Error loading sudoku.\n");
    return 1;
  }

  /* Generate the model.c file. */
  if (createModel(sudoku, NULL, 0) == 1) {
    fprintf(stderr, "Error creating model file.\n");
    return 1;
  }

  /* Run CBMC model checker. */
  if (mode == 0) {
    /* Basic checker. */
    runCBMC();
    if (printSudoku() == 1) {
      printf("UNSOLVABLE\n");
    }
  } else if (mode == 1) {
    /* Exhaustive checker. */
    int solutionCount = 0;
    unsigned long hashes[MAXSOLUTIONS];

    /* Search for all solutions. */
    while (solutionCount < MAXSOLUTIONS) {
      int solution[81];

      runCBMC();
      if (printSudoku() == 1) {
        /* No remaining solutions. */
        break;
      }

      /* Print newline between puzzles. */
      if (silentMode == 0) {
        printf("\n");
      }
      solutionCount++;

      /* Get solution and create hash to update the model. */
      if (readSudoku("output.txt", solution) == 1) {
        fprintf(stderr, "Error loading solution.\n");
        return 1;
      }

      unsigned long hash = hashArray(solution);
      hashes[solutionCount] = hash;

      if (createModel(sudoku, hashes, solutionCount) == 1) {
        fprintf(stderr, "Error creating updated model file.\n");
        return 1;
      }
    }

    printf("NUMBER OF SOLUTIONS: %d\n", solutionCount);
  }

  return 0;
}

int readSudoku(char *fileName, int sudoku[81]) {
  FILE *inputFile = fopen(fileName, "r");
  if (inputFile == NULL) {
    return 1;
  }

  /* Scan each digit into 1D array. */
  for (int i = 0; i < 81; ++i) {
    if (fscanf(inputFile, "%d", &sudoku[i]) != 1) {
      fclose(inputFile);
      return 1;
    }
  }

  fclose(inputFile);

  return 0;
}

int createModel(int sudoku[81], unsigned long hashes[100], int solutionCount) {
  FILE *outputFile = fopen("model.c", "w");
  if (outputFile == NULL) {
    return 1;
  }

  fprintf(outputFile, "#include <stdint.h>\n\n");

  fprintf(outputFile, "#define INDEX(row, col) ((row) * 9 + (col))\n\n");

  fprintf(outputFile, "int nondet_int();\n\n");

  fprintf(outputFile, "int main(int argc, char *argv[]) {\n");
  fprintf(outputFile, "  /* Sudoku structure. */\n");
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

  fprintf(outputFile, "  /* Create nondeterministic search space for empty cells. */\n");
  fprintf(outputFile, "  for (int i = 0; i < 9; ++i) {\n");
  fprintf(outputFile, "    for (int j = 0; j < 9; ++j) {\n");
  fprintf(outputFile, "      if (sudoku[INDEX(i, j)] == 0) {\n");
  fprintf(outputFile, "        int cell = nondet_int();\n");
  fprintf(outputFile, "        __CPROVER_assume(cell >= 1 && cell <= 9);\n");
  fprintf(outputFile, "        sudoku[INDEX(i, j)] = cell;\n");
  fprintf(outputFile, "      }\n");
  fprintf(outputFile, "    }\n");
  fprintf(outputFile, "  }\n\n");

  if (mode == 1) {
    fprintf(outputFile, "  /* Ensure unique solution. */\n");
    fprintf(outputFile, "  unsigned long hash = 0;\n");
    fprintf(outputFile, "  for (int i = 0; i < 81; i++) {\n");
    fprintf(outputFile, "    hash = (hash * 37) + sudoku[i];\n");
    fprintf(outputFile, "  }\n");

    for (int i = 1; i <= solutionCount; i++) {
      fprintf(outputFile, "  __CPROVER_assume(hash != %luul);\n", hashes[i]);
    }
  }

  fprintf(outputFile, "\n");

  fprintf(outputFile, "  /* Bit masks for uniqueness and efficiency. */\n");
  fprintf(outputFile, "  uint16_t rows[9] = {0};\n");
  fprintf(outputFile, "  uint16_t cols[9] = {0};\n");
  fprintf(outputFile, "  uint16_t blocks[9] = {0};\n\n");

  fprintf(outputFile, "  for (int i = 0; i < 9; i++) {\n");
  fprintf(outputFile, "    for (int j = 0; j < 9; j++) {\n");
  fprintf(outputFile, "      int val = sudoku[INDEX(i, j)];\n");
  fprintf(outputFile, "      int bit = 1 << (val - 1);\n\n");

  fprintf(outputFile, "      /* Each number appears at most once in each row. */\n");
  fprintf(outputFile, "      __CPROVER_assume(!(rows[i] & bit));\n");
  fprintf(outputFile, "      /* Each number appears at most once in each col. */\n");
  fprintf(outputFile, "      __CPROVER_assume(!(cols[j] & bit));\n");
  fprintf(outputFile, "      /* Each number appears at most once in each block. */\n");
  fprintf(outputFile, "      __CPROVER_assume(!(blocks[(i / 3) * 3 + j / 3] & bit));\n\n");
  fprintf(outputFile, "      /* Set as seen. */\n");
  fprintf(outputFile, "      rows[i] |= bit;\n");
  fprintf(outputFile, "      cols[j] |= bit;\n");
  fprintf(outputFile, "      blocks[(i / 3) * 3 + j / 3] |= bit;\n");
  fprintf(outputFile, "    }\n");
  fprintf(outputFile, "  }\n\n");

  fprintf(outputFile, "  /* Start search. */\n");
  fprintf(outputFile, "  __CPROVER_assert(0, \"Search.\");\n");

  fprintf(outputFile, "  return 0;\n");
  fprintf(outputFile, "}\n");

  fclose(outputFile);

  return 0;
}

void runCBMC() {
  /* Execute system command and use pipelines to save the cell values in output.txt. */
  system("/home/milan/.repos/cbmc-cbmc-5.90.0/src/cbmc/cbmc --trace model.c | grep -o 'val=[0-9]\\+' | cut -d '=' -f 2 > output.txt");
}

int printSudoku() {
  FILE *inputFile = fopen("output.txt", "r");
  if (inputFile == NULL) {
    return 1;
  }

  /* Only print when not silent mode. */
  if (silentMode == 0) {
    for (int i = 0; i < 9; i++) {
      for (int j = 0; j < 9; j++) {
        int num;
        if (fscanf(inputFile, "%d", &num) != 1) {
          /* No solution found. */
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
  } else {
    /* Check for a solution. */
    if (fgetc(inputFile) == EOF) {
      fclose(inputFile);
      return 1;
    }
  }

  fclose(inputFile);
  return 0;
}

unsigned long hashArray(int arr[]) {
  /* Hash using a large prime to minimise collisions. */
  unsigned long hash = 0;
  for (int i = 0; i < 81; i++) {
    hash = (hash * 37) + arr[i];
  }
  return hash;
}