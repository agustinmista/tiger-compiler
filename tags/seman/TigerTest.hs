module TigerTest (runTestDirs, runTest) where

import System.Environment
import System.Directory
import System.Console.ANSI
import Data.List

import Control.Applicative
import Control.Monad
import System.FilePath ( (</>) )
import qualified TigerMain as Tiger
import System.IO.Unsafe ( unsafeInterleaveIO )


runTestDirs :: [String] -> String -> IO ()
runTestDirs args dir = do
    tests <- getRecursiveContents dir 
    res <- mapM (runTest args) (sort tests) 
    printHeader
    mapM_ printWithColor res

runTest :: [String] -> String -> IO (String, Int)
runTest args path = do
    printTestHeader path
    res <- withArgs (path:args) Tiger.main
    return (path, res)

getRecursiveContents :: FilePath -> IO [FilePath]
getRecursiveContents topPath = do
  names <- unsafeInterleaveIO $ getDirectoryContents topPath
  let properNames = filter (`notElem` [".", ".."]) names
  paths <- forM properNames $ \name -> do
    let path = topPath </> name
    isDirectory <- doesDirectoryExist path
    if isDirectory
      then unsafeInterleaveIO $ getRecursiveContents path
      else return [path]
  return (concat paths)

printTestHeader :: String -> IO () 
printTestHeader path = do
    setSGR [SetColor Foreground Vivid Yellow]
    putStrLn path  
    setSGR [Reset]

printHeader :: IO () 
printHeader = do
    putStrLn "+--------------------------------------------------------+"
    putStrLn "|                         SUMMARY                        |"
    putStrLn "+--------------------------------------------------------+"

                    
printWithColor :: (String, Int) -> IO ()
printWithColor (t,r) = do
    putStr $ t ++ " -> "
    if r == 0 
        then setSGR [SetColor Foreground Vivid Green] >> putStrLn "[OK]"
        else setSGR [SetColor Foreground Vivid Red]   >> putStrLn "[FAIL]"
    setSGR [Reset]
