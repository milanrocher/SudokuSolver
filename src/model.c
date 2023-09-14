int main(int argc, char *argv[]) {
  int sudoku[9][9] = {
    {0, 1, 0, 0, 0, 6, 4, 0, 0},
    {0, 9, 0, 4, 5, 0, 0, 2, 0},
    {5, 0, 0, 0, 0, 7, 0, 0, 0},
    {0, 0, 0, 0, 0, 5, 0, 0, 0},
    {9, 0, 0, 1, 8, 0, 7, 0, 0},
    {0, 2, 0, 0, 0, 0, 0, 0, 3},
    {8, 0, 0, 9, 4, 0, 1, 0, 0},
    {0, 0, 0, 6, 0, 0, 0, 0, 0},
    {0, 0, 1, 0, 0, 0, 0, 7, 0},
  };

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
      for (int k = j + 1; k < 9; k++) {
        __CPROVER_assume(sudoku[i][k] != val);
      }

      for (int k = i + 1; k < 9; k++) {
        __CPROVER_assume(sudoku[k][j] != val);
      }

      int block_row = i / 3 * 3;
      int block_col = j / 3 * 3;
      for (int m = block_row; m < block_row + 3; m++) {
        for (int n = block_col; n < block_col + 3; n++) {
          if (m != i || n != j) {
            __CPROVER_assume(sudoku[m][n] != val);
          }
        }
      }
    }
  }

  assert(0);

  return 0;
}
