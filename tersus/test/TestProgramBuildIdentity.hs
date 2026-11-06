{-# LANGUAGE TemplateHaskell #-}

module TestProgramBuildIdentity (concreteBuildIdentity, concreteBuildDescription, approvedBuildIdentity) where

import Control.DeepSeq (force)
import qualified Data.Binary as Binary
import qualified Data.ByteString.Lazy as BL
import Data.Char (isHexDigit, toLower)
import qualified Data.Map.Strict as Map
import Data.Version (showVersion)
import Hash (fingerprint)
import Language.Haskell.TH.Syntax (lift, namePackage, runIO)
import qualified System.Directory as Directory
import qualified System.Environment as Environment
import System.Info (arch, compilerName, compilerVersion, os)
import qualified System.Posix.IO as Posix
import qualified System.Process as Process
import qualified Text.Parsec as Parsec

-- Reified package identities describe the packages actually selected by GHC,
-- including direct ghc builds: no ghc-pkg subprocess or Cabal macro guessing.
concreteBuildIdentity :: String
concreteBuildIdentity = fingerprint concreteBuildDescription

concreteBuildDescription :: [String]
concreteBuildDescription =
    [ compilerName, showVersion compilerVersion, os, arch
    , $(lift (show (map namePackage
        [ 'id, 'Map.fromList, 'Binary.encode, 'BL.fromStrict, 'force
        , 'Directory.getXdgDirectory, 'Process.readProcessWithExitCode
        , 'Posix.openFd, 'Parsec.parse, 'lift
        ])))
    ]

-- This is a build-time opt-in, not a runtime override. It must name an approved
-- complete build-options manifest; source, codec and concrete package identity
-- are still separate key inputs. With no approval, TestHarness hashes its actual
-- executable conservatively because public TH does not expose all GHC options.
approvedBuildIdentity :: Maybe String
approvedBuildIdentity = $(do
    approved <- runIO (Environment.lookupEnv "TERSUS_TEST_APPROVED_BUILD_IDENTITY")
    case approved of
        Nothing -> lift (Nothing :: Maybe String)
        Just value
            | length value == 64 && all isHexDigit value -> lift (Just (map toLower value))
            | otherwise -> fail "TERSUS_TEST_APPROVED_BUILD_IDENTITY must be the SHA256 of an explicitly approved complete build-options manifest")
