------------------------------------------------------------------------------
--- Operations to show and store statistical information about the analysis.
---
--- @author Michael Hanus
--- @version October 2023
-----------------------------------------------------------------------------

module Verify.Statistics ( showStatistics, storeStatistics )
  where

import Control.Monad        ( when )

import AbstractCurry.Types  ( QName )
import Analysis.TermDomain  ( TermDomain )
import Text.CSV

import Verify.CallTypes
import Verify.IOTypes
import Verify.Options

------------------------------------------------------------------------------
-- Definition of directory and file names for various data.

-- The name of the file containing statistical information about the
-- verification of a module.
statsFile :: String -> String
statsFile mname = mname ++ "-STATISTICS"

-- Show statistics in textual and in CSV format:
showStatistics :: TermDomain a => Options -> Int -> Int -> (QName -> Bool)
               -> Int -> Int -> (Int,Int)
               -> (Int,Int) -> [(QName, ACallType a)]
               -> (Int,Int) -> (String, [String])
showStatistics opts vtime numits isvisible numvisfuncs numallfuncs
               (numpubiotypes, numalliotypes)
               (numpubcalltypes, numallcalltypes)
               ntfinalcts (numcalls, numcases) =
  ( unlines $
      [ "Functions                      (public / all): " ++
        show numvisfuncs ++ " / " ++ show numallfuncs
      , "Non-trivial input/output types (public / all): " ++
        show numpubiotypes ++ " / " ++ show numalliotypes
      , "Initial non-trivial call types (public / all): " ++
        show numpubcalltypes ++ " / " ++ show numallcalltypes ] ++
      (if optVerify opts
         then [ "Final non-trivial call types   (public / all): " ++
                show numntfinalpubcts ++ " / " ++ show numntfinalcts
              , "Final failing call types       (public / all): " ++
                show numfailpubcts ++ " / " ++ show numfailcts
              , "Non-trivial function calls checked           : " ++
                show numcalls
              , "Incomplete case expressions checked          : " ++
                show numcases
              , "Number of iterations for call-type inference : " ++
                show numits
              , "Total verification in msecs                  : " ++
                show vtime ]
         else [])
  , map show [ numvisfuncs, numallfuncs, numpubiotypes, numalliotypes
             , numpubcalltypes, numallcalltypes
             , numntfinalpubcts, numntfinalcts
             , numfailpubcts, numfailcts
             , numcalls, numcases, numits, vtime ]
  )
 where
  ntfinalpubcts    = filter (isvisible . fst) ntfinalcts
  numntfinalpubcts = length ntfinalpubcts
  numntfinalcts    = length ntfinalcts
  numfailpubcts    = length (filter (isFailACallType . snd) ntfinalpubcts)
  numfailcts       = length (filter (isFailACallType . snd) ntfinalcts)

--- Store the statitics for a module in a text and a CSV file
--- (if required by the current options).
storeStatistics :: Options -> String -> String -> [String] -> IO ()
storeStatistics opts mname stattxt statcsv = when (optStats opts) $ do
  reportWriting writeFile    (statsFile mname ++ ".txt") stattxt
  reportWriting writeCSVFile (statsFile mname ++ ".csv") [mname : statcsv]
 where
  reportWriting wf f s = do
    when (optVerb opts > 2) $ putStr $ "Storing statistics in '" ++ f ++ "'..."
    wf f s
    printWhenAll opts "done"

------------------------------------------------------------------------------
