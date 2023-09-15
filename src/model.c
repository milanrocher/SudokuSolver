#include <stdio.h>
#include <stdint.h>

#define INDEX(row, col) ((row) * 9 + (col))

int main(int argc, char *argv[]) {
  /*
   * Sudoku structure.
   */
  int sudoku[81] = {
      0, 1, 0, 0, 0, 6, 4, 0, 0,
      0, 9, 0, 4, 5, 0, 0, 2, 0,
      5, 0, 0, 0, 0, 7, 0, 0, 0,
      0, 0, 0, 0, 0, 5, 0, 0, 0,
      9, 0, 0, 1, 8, 0, 7, 0, 0,
      0, 2, 0, 0, 0, 0, 0, 0, 3,
      8, 0, 0, 9, 4, 0, 1, 0, 0,
      0, 0, 0, 6, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 7, 0,
  };

  /*
   * Create nondeterministic search space for empty cells.
   */
  for (int i = 0; i < 9; ++i) {
    for (int j = 0; j < 9; ++j) {
      if (sudoku[INDEX(i, j)] == 0) {
        int cell = nondet_int();
        __CPROVER_assume(cell >= 1 && cell <= 9);
        sudoku[INDEX(i, j)] = cell;
      }
    }
  }

  /*
   * Bit maks for uniqueness
   */
  uint16_t rows[9] = {0};
  uint16_t cols[9] = {0};
  uint16_t blocks[9] = {0};

  for (int i = 0; i < 9; i++) {
    for (int j = 0; j < 9; j++) {
      int val = sudoku[INDEX(i, j)];
      int bit = 1 << (val - 1);

      /*
       * Each number appears at most once in each row.
       */
      __CPROVER_assume(!(rows[i] & bit));
      /*
       * Each number appears at most once in each col.
       */
      __CPROVER_assume(!(cols[j] & bit));
      /*
       * Each number appears at most once in each block.
       */
      __CPROVER_assume(!(blocks[(i / 3) * 3 + j / 3] & bit));

      /*
       * Set as seen.
       */
      rows[i] |= bit;
      cols[j] |= bit;
      blocks[(i / 3) * 3 + j / 3] |= bit;
    }
  }

  /*
   * Start search.
   */
  assert(0);

  return 0;
}
