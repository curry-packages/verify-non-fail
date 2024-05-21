verify-non-fail: A tool to verify Curry operations as non-failing
=================================================================

This package contains a tool to verify that all operations
in a given module are non-failing, i.e., their evaluation does
not result in a failure, if they are called with appropriate
arguments. The tool automatically infers abstract call types
specifying supersets of appropriate arguments.

As an example, consider the following operation to compute the last element
of a given list:

    last :: [a] -> a
    last [x]            = x
    last (_ : xs@(_:_)) = last xs

In the default mode (where types are abstracted into a set
of allowed top-level constructors), the inferred call type is

    last: {:}

specifying that `last` does not fail if the argument is a
non-empty list, i.e., evaluable to some data term rooted by
the list constructor "`:`".

When an operation with such a restricted call type is used,
the tool checks whether it is used in a context which
ensures its call type. For instance, the operations

    head (x:xs) = x

and

    tail (x:xs) = xs

have the inferred call types

    head: {:}
    tail: {:}

When these operations are applied, it should be ensured
(in a top-level functional computation) that the actual arguments
are non-empty lists, as in the following operation:

    readCommand :: IO ()
    readCommand = do
      putStr "Input a command:"
      s <- getLine
      let ws = words s
      case null ws of True  -> readCommand
                      False -> processCommand (head ws) (tail ws)

The tool automatically verifies that the operation `readCommand`
is non-failing.

The ideas of the implementation of this tool are described in:

M. Hanus: Inferring Non-Failure Conditions for Declarative Programs,
Proc. of the 17th International Symposium on Functional and Logic Programming
(FLOPS 2024), to appear in Springer LNCS, 2024


Arithmetic non-fail conditions (experimental extension!)
--------------------------------------------------------

If the SMT solver [Z3](https://github.com/Z3Prover/z3.git) is
installed and the executable `z3` can be found in the path,
the tool can also infer and verify arithmetic non-fail conditions.
For instance, it infers for the factorial function defined by

    fac :: Int -> Int
    fac n | n == 0 = 1
          | n > 0  = n * fac (n - 1)

the non-fail condition

    fac'nonfail :: Int -> Bool
    fac'nonfail v1 = (v1 == 0) || (v1 > 0)

specifying that the argument must be non-negative in order to ensure
that `fac` does not fail.
With this information, it also proves that the following
I/O operation does not fail (where the operation `readInt`
reads a line until it is an integer):

    printFac :: IO ()
    printFac = do
      putStr "Factorial computation for: "
      n <- readInt
      if n<0 then putStrLn "Negative number, try again" >> printFac
             else print (fac n)


------------------------------------------------------------------------------

Installation:
-------------

The tool can be installed via the command

    > cypm install

in the main directory of this package.
This installs the executable `curry-calltypes` in the bin-directory of CPM.

If one use KiCS2 to install this tool, one should use version 3.1.0
of April 11, 2024 (or newer) due to a memory leak in an older version of KiCS2.

------------------------------------------------------------------------------
