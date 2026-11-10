module ElaboratorNative where

import Utils (Result)

frontendStage :: Int -> IO (Result (FilePath, String) String)
