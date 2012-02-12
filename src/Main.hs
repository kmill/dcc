module Main where

import IO
import System.Environment
import CLI
import Data.Maybe (fromMaybe)
import Scanner
import Parser

main :: IO ()
main = do args <- getArgs
          opts <- compilerOpts args
          let ifname = fromMaybe "<stdin>" $ inputFile opts
          input <- case inputFile opts of
                     Just ifname -> readFile ifname
                     Nothing -> hGetContents stdin
          case target opts of
            TargetScanner -> doScanFile opts ifname input
            _ -> error "No such target"

printScannerResult :: [Token] -> IO ()
printScannerResult (t:ts) = do putStrLn $ show t
                               printScannerResult ts
printScannerResult [] = return ()

doScanFile opts ifname input
    = case runScanner opts ifname input of
        Left err -> print err
        Right v -> printScannerResult v
