#include <stdint.h>

#define INDEX(row, col) ((row) * 9 + (col))

int nondet_int();

int main(int argc, char *argv[]) {
  /* Sudoku structure. */
  int sudoku[81] = {
      2, 9, 5, 7, 4, 3, 8, 6, 1,
      4, 3, 1, 8, 6, 5, 9, 0, 0,
      8, 7, 6, 1, 9, 2, 5, 4, 3,
      3, 8, 7, 4, 5, 9, 2, 1, 6,
      6, 1, 2, 3, 8, 7, 4, 9, 5,
      5, 4, 9, 2, 1, 6, 7, 3, 8,
      7, 6, 3, 5, 2, 4, 1, 8, 9,
      9, 2, 8, 6, 7, 1, 3, 5, 4,
      1, 5, 4, 9, 3, 8, 6, 0, 0,
  };

  /* Create nondeterministic search space for empty cells. */
  for (int i = 0; i < 9; ++i) {
    for (int j = 0; j < 9; ++j) {
      if (sudoku[INDEX(i, j)] == 0) {
        int cell = nondet_int();
        __CPROVER_assume(cell >= 1 && cell <= 9);
        sudoku[INDEX(i, j)] = cell;
      }
    }
  }

  /* Ensure unique solution. */
  unsigned long hash = 0;
  for (int i = 0; i < 81; i++) {
    hash = (hash * 37) + sudoku[i];
  }
  __CPROVER_assume(hash != 6568365452116789893ul);
  __CPROVER_assume(hash != 6427881628716596085ul);

  /* Bit masks for uniqueness and efficiency. */
  uint16_t rows[9] = {0};
  uint16_t cols[9] = {0};
  uint16_t blocks[9] = {0};

  for (int i = 0; i < 9; i++) {
    for (int j = 0; j < 9; j++) {
      int val = sudoku[INDEX(i, j)];
      int bit = 1 << (val - 1);

      /* Each number appears at most once in each row. */
      __CPROVER_assume(!(rows[i] & bit));
      /* Each number appears at most once in each col. */
      __CPROVER_assume(!(cols[j] & bit));
      /* Each number appears at most once in each block. */
      __CPROVER_assume(!(blocks[(i / 3) * 3 + j / 3] & bit));

      /* Set as seen. */
      rows[i] |= bit;
      cols[j] |= bit;
      blocks[(i / 3) * 3 + j / 3] |= bit;
    }
  }

  /* Start search. */
  __CPROVER_assert(0, "Search.");
  return 0;
}
