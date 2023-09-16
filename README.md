# Software Verification and Analysis
### C Bounded Model Checker
This Sudoku solver is implemented in C and uses the CBMC tool to verify and find solutions for Sudoku puzzles.

It provides two modes of operation:
- basic checking and
- exhaustive searching for multiple solutions.

## Requirements
- C for compiling the wrapper.
- CBMC v5.90.0 for model checking.

## Usage
Enter the [source](./src/) directory.

### Step 1
Add a sudoku puzzle in a text file in the same format as below:

0 1 0 0 0 6 4 0 0 \
0 9 0 4 5 0 0 2 0 \
5 0 0 0 0 7 0 0 0 \
0 0 0 0 0 5 0 0 0 \
9 0 0 1 8 0 7 0 0 \
0 2 0 0 0 0 0 0 3 \
8 0 0 9 4 0 1 0 0 \
0 0 0 6 0 0 0 0 0 \
0 0 1 0 0 0 0 7 0

### Step 2
Compile the wrapper:

```commandline
gcc wrapper.c -o wrapper
```

### Step 3
Run the wrapper, one of three ways:

```commandline
./wrapper --basic <path/to/input_file.txt>
```

```commandline
./wrapper --exhaustive <path/to/input_file.txt>
```

```commandline
./wrapper --exhaustive --silent <path/to/input_file.txt>
```

## Solving Process

### Wrapper
The wrapper is in charge of the whole execution process and creating the model.

1. The Sudoku puzzle is read from an input file and stored in memory.
2. The program generates a CBMC model file (model.c) that includes constraints and assumptions for the Sudoku puzzle.
   This was chosen as using external data structures does not work if CBMC is used to compile the model.c file.
   Furthermore, the minimal encodings were used from [here](./research/sudoku-as-SAT.pdf).
3. Basic Mode: \
   3.1. The CBMC tool is started on the generated model file. \
   3.2. The solution is printed to standard output, or if no solution is found, "UNSOLVABLE" is printed.
4. Exhaustive Mode: \
   4.1. A solution count and list of hashes are initialised. \
   4.2. Run the CBMC tool on the generated model file in a loop. \
   4.3. The solution is printed to standard output (if not silenced). \
   4.4. Save the solution in an array and calculate a hash value for the puzzle. \
   4.5. Generate a new CBMC model file which now also includes the hashes found thus far and assumptions
        which guarantee unique solutions. \
   4.6. Print the number of solution found.

### Model Checker
The model file (created by the wrapper) describes the Sudoku model using CBMC functions.

1. Load the puzzle into a 1D array to save memory.
2. Create a nondeterministic search space for all the empty cell.
3. Cells are assumed to be values between 1 and 9 (both inclusive).
4. If an exhaustive search is in process, assume a unique hash value for the new solution.
5. To enforce the uniqueness of numbers in rows, columns, and blocks, bit masks are used (more efficient than integer
   arrays).
6. Assumptions are added to the model to check that no number repeats within these masks.
7. The CBMC search is started with a failing assertion.

## Author
Milan Rocher \
23642114
