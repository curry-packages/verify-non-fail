verify-non-fail: A tool to verify Curry operations as non-failing
=================================================================

This package contains a tool to verify that all operations
in a given module are non-failing, i.e., tehir evaluation does
not result in a failure, if they are called with appropriate
arguments. The tool automatically infers abstract call types
specifying supersets of appropriate arguments.

As am example, consider the following operation to compute the last element
of a given list:

    last :: [a] -> a
    last [x]            = x
    last (_ : xs@(_:_)) = last xs

In the default mode (where types are abstracted into a set
of allowed top-level constructors), the inferred call type is

    last: {:}

specifying that `last` does not fail if the argument is a
non-empty list, i.e., evaluable to some data term rooted by
the list constructor `:`.

When an operation with such a restricted call type is used,
the tool checks whether it is used in an environment which
ensures its call type. For instance, the operations

    head (x:xs) = x

and

    tail (x:xs) = xs

have the inferred call types

    head: {:}
    tail: {:}

When these operations are applied, it should be ensure
(in a top-level functional computation) that the actual arguments
are non-empty lists, as in this operation:

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

------------------------------------------------------------------------------

Installation:
-------------

The tool can be installed via the command

    > cypm install

in the main directory of this package.
This installs the executable `curry-calltypes` in the bin-directory of CPM.

Installation with KiCS2:
------------------------

Due to an unresolved memory leak in KiCS2,
it is necessary to generate different executables for each
abstract domain used by the inferences.
This can be done by executing

    > make

in the main directory of this package.
This installs the executable `curry-calltypes` as well as three
other executables which are implicitly invoked by the main
executable in the bin-directory of CPM.

------------------------------------------------------------------------------
