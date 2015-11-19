module Paths_lambda_pi_constraint (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/joey/thesis/lambda-pi-constraint/.cabal-sandbox/bin"
libdir     = "/home/joey/thesis/lambda-pi-constraint/.cabal-sandbox/lib/x86_64-linux-ghc-7.10.2.20151105/lambda-pi-constraint-0.1.0.0-6obHekjG3XB6ko8XRkKwlp"
datadir    = "/home/joey/thesis/lambda-pi-constraint/.cabal-sandbox/share/x86_64-linux-ghc-7.10.2.20151105/lambda-pi-constraint-0.1.0.0"
libexecdir = "/home/joey/thesis/lambda-pi-constraint/.cabal-sandbox/libexec"
sysconfdir = "/home/joey/thesis/lambda-pi-constraint/.cabal-sandbox/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "lambda_pi_constraint_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "lambda_pi_constraint_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "lambda_pi_constraint_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "lambda_pi_constraint_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "lambda_pi_constraint_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
