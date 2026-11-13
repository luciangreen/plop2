-- | Build and test plop2 with plain GHC against detlog2's sources.
--
--   runghc Build.hs          build build/plop2
--   runghc Build.hs test     build, then run the end-to-end tests
--   runghc Build.hs ci       as test; fetches detlog2 (and mnns) when they are not given
--
-- DETLOG2_DIR (default ../detlog2) and MNNS_DIR select the other repositories.
module Main (main) where

import Control.Monad (unless, when)
import System.Directory (createDirectoryIfMissing, doesDirectoryExist)
import System.Environment (getArgs, lookupEnv, setEnv)
import System.Exit (ExitCode(..), exitWith)
import System.Process (rawSystem)

main :: IO ()
main = do
  args <- getArgs
  createDirectoryIfMissing True "build"
  let ci = take 1 args == ["ci"]
  detlog2 <- repo "DETLOG2_DIR" "../detlog2" "build/detlog2-src" "https://github.com/luciangreen/detlog2" ci
  when ci $ () <$ repo "MNNS_DIR" "../mnns" "build/mnns" "https://github.com/luciangreen/mnns" True
  run "ghc" (["-O1", "-Wall", "-Wno-incomplete-uni-patterns", "-Wno-name-shadowing", "-Wno-unused-do-bind"]
             ++ ["-isrc", "-i" ++ detlog2 ++ "/src", "-outputdir", "build", "-o", "build/plop2", "app/Main.hs"])
  when (take 1 args `elem` [["test"], ["ci"]]) $ do
    -- detlog2's own binary runs the generated files in the tests
    run "ghc" ["-O1", "-i" ++ detlog2 ++ "/src", "-outputdir", "build/d2", "-o", "build/detlog2", detlog2 ++ "/app/Main.hs"]
    run "ghc" ["-O0", "-outputdir", "build/t", "-o", "build/cli-tests", "tests/Cli.hs"]
    run "./build/cli-tests" []

-- | A sibling repository: from the environment, next to this one, or cloned.
repo :: String -> FilePath -> FilePath -> String -> Bool -> IO FilePath
repo var sibling cloneDir url mayClone = do
  m <- lookupEnv var
  dir <- case m of
    Just d -> return d
    Nothing -> do
      haveSibling <- doesDirectoryExist sibling
      if haveSibling then return sibling else do
        haveClone <- doesDirectoryExist cloneDir
        unless (haveClone || not mayClone) $ run "git" ["clone", "--depth", "1", url, cloneDir]
        return cloneDir
  setEnv var dir
  return dir

run :: String -> [String] -> IO ()
run cmd as = do
  code <- rawSystem cmd as
  when (code /= ExitSuccess) $ exitWith code
