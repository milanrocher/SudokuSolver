#ifndef BMC_WRAPPER_H
#define BMC_WRAPPER_H

/**
 * This function reads a Sudoku puzzle from the specified file and stores it in
 * the given integer array representing the Sudoku grid.
 *
 * @param fileName  The name of the input file containing the Sudoku puzzle.
 * @param sudoku    A pointer to an integer array where the Sudoku puzzle will be stored.
 * @return          0 on success.
 *                  \n
 *                  1 on failure.
 */
int readSudoku(char *fileName, int sudoku[81]);

/**
 * This function prints the Sudoku puzzle, which should be stored in 'output.txt'.
 * The puzzle is printed to the standard output in a readable format.
 * \n
 * There is a silent mode, in which standard output is not printed.
 *
 * @return 0 on success.
 *         \n
 *         1 on failure.
 */
int printSudoku();

/**
 * This function generates a CBMC model in a separate file for the given Sudoku puzzle.
 * The model includes assumptions to be used by the CBMC model checker.
 * Additionally, it accepts an array of hashes representing previously found puzzle
 * solutions and the count of solutions found.
 *
 * @param sudoku        A pointer to an integer array containing the Sudoku puzzle.
 * @param hashes        An array of unsigned long integers representing hash values
 *                      of previously found puzzle solutions.
 * @param solutionCount The number of solutions found so far.
 * @return              0 on success.
 *                      \n
 *                      1 on failure.
 */
int createModel(int sudoku[81], unsigned long hashes[100], int solutionCount);

/**
 * This function invokes the CBMC model checker on the generated CBMC model file.
 */
void runCBMC();

/**
 * This function calculates a hash value for the given integer array. It can be used
 * to generate a unique identifier for a Sudoku puzzle solution.
 *
 * @param arr   A pointer to an integer array for which the hash will be calculated.
 * @return      The calculated hash value as an unsigned long integer.
 */
unsigned long hashArray(int arr[]);

#endif
