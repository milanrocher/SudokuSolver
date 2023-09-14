int main(int argc, char *argv[]) {
  /*
  * Sudoku structure.
  */
  int sudoku[9][9] = {
    {0, 1, 0, 0, 0, 6, 4, 0, 4},
    {0, 9, 0, 4, 5, 0, 0, 2, 0},
    {5, 0, 0, 0, 0, 7, 0, 0, 0},
    {0, 0, 0, 0, 0, 5, 0, 0, 0},
    {9, 0, 0, 1, 8, 0, 7, 0, 0},
    {0, 2, 0, 0, 0, 0, 0, 0, 3},
    {8, 0, 0, 9, 4, 0, 1, 0, 0},
    {0, 0, 0, 6, 0, 0, 0, 0, 0},
    {0, 0, 1, 0, 0, 0, 0, 7, 0},
  };

  /*
  * Create nondeterministic search space for empty cells.
  */
  for (int i = 0; i < 9; ++i) {
    for (int j = 0; j < 9; ++j) {
      if (sudoku[i][j] == 0) {
        int cell = nondet_int();
        __CPROVER_assume(cell >= 1 && cell <= 9);
        sudoku[i][j] = cell;
      }
    }
  }

  for (int i = 0; i < 9; i++) {
    for (int j = 0; j < 9; j++) {
      int val = sudoku[i][j];
      /*
      * There is at least one number in each entry.
      */
      __CPROVER_assume(val != 0);

      /*
      * Each number appears at most once in each row.
      */
      for (int k = j + 1; k < 9; k++) {
        __CPROVER_assume(sudoku[i][k] != val);
      }

      /*
      * Each number appears at most once in each col.
      */
      for (int k = i + 1; k < 9; k++) {
        __CPROVER_assume(sudoku[k][j] != val);
      }

      /*
      * Each number appears at most once in each block.
      */
      int blockRow = i / 3 * 3;
      int blockCol = j / 3 * 3;
      for (int m = blockRow; m < blockRow + 3; m++) {
        for (int n = blockCol; n < blockCol + 3; n++) {
          if (m != i || n != j) {
            __CPROVER_assume(sudoku[m][n] != val);
          }
        }
      }
    }
  }

  /*
  * Start search.
  */
  assert(0);

  return 0;
}
