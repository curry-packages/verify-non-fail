A tool to verify Curry operations as non-failing
================================================

This package contains a tool to verify that all operations
in a given Curry module are non-failing, i.e., their evaluation does
not result in a failure, if they are called with appropriate
arguments. The tool automatically infers abstract call types
and non-fail conditions specifying supersets of appropriate arguments.

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

> M. Hanus: Inferring Non-Failure Conditions for Declarative Programs,
> Proc. of the 17th International Symposium on Functional and Logic Programming
> (FLOPS 2024), Springer LNCS 14659, pp. 167-187, 2024,
> DOI: [10.1007/978-981-97-2300-3\_10](http://dx.doi.org/10.1007/978-981-97-2300-3\_10),


Arithmetic non-fail conditions
------------------------------

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

Installation
------------

If you downloaded the sources of this package, then the tool can be
installed via the command

    > cypm install

in the main directory of this package. Otherwise, the tool can
also be downloaded and installed by the command

    > cypm install verify-non-fail

This installs the executable `curry-calltypes` in the bin-directory of CPM.

If one uses KiCS2 to install this tool, one should use version 3.1.0
of April 11, 2024 (or newer) due to a memory leak in an older version of KiCS2.

------------------------------------------------------------------------------

Web Demo Installation
---------------------

If you want to try this tool on simple programs via a web interface,
you can use a
[Web Demo Installation](https://cpm.curry-lang.org/webapps/failfree/)
of this tool.

------------------------------------------------------------------------------

Files
-----

In order to support a modular analysis of applications consisting
of several modules, the tool caches already computed analysis results
of modules in under the directory `~/.curry_verify_cache`.
This path is defined in `Verify.Files.getVerifyCacheDirectory`.
To store the analysis results for different Curry systems and
abstract domains separately, the analysis results for a Curry module
which is stored in a file with path `MODULEPATH.curry` are contained in

    ~/.curry_verify_cache/CURRYSYSTEMID/DOMAINID/MODULEPATH-*

For instance, the call types of the prelude for KiCS2 Version 3.1.0
w.r.t. the abstract domain `Values` are stored in

    ~/.curry_verify_cache/kics2-3.1.0/Values/opt/kics2/lib/Prelude-CALLTYPES

provided that KiCS2 is installed at `/opt/kics2` so that the prelude
is contained in the file `/opt/kics2/lib/Prelude.curry`.

All cache files (for the Curry system used to install this tool)
can be deleted by the command

    curry-calltypes --delete

------------------------------------------------------------------------------
