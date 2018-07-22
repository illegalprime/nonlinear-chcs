{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -fno-warn-implicit-prelude #-}
module Paths_mscrt (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/michael/.cabal/bin"
libdir     = "/home/michael/.cabal/lib/x86_64-linux-ghc-8.2.2/mscrt-0.1.0.0-ITbVasAQMZABTOfxLc4YLy-mscrt"
dynlibdir  = "/home/michael/.cabal/lib/x86_64-linux-ghc-8.2.2"
datadir    = "/home/michael/.cabal/share/x86_64-linux-ghc-8.2.2/mscrt-0.1.0.0"
libexecdir = "/home/michael/.cabal/libexec/x86_64-linux-ghc-8.2.2/mscrt-0.1.0.0"
sysconfdir = "/home/michael/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "mscrt_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "mscrt_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "mscrt_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "mscrt_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "mscrt_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "mscrt_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
