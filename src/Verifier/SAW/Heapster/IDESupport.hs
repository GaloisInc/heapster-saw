{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Heapster.IDESupport where

import Data.Aeson ( encodeFile, ToJSON )
import Data.Binding.Hobbits
    ( nuMP,
      mbMatch,
      unsafeMbTypeRepr,
      Liftable(..),
      Mb,
      NuMatching(..) )
import Data.Parameterized.Some (Some (..))
import qualified Data.Text as T
import qualified Data.Type.RList as RL
import GHC.Generics ( Generic )
import What4.FunctionName ( FunctionName(functionName) )
import What4.ProgramLoc
    ( Position(InternalPos, SourcePos, BinaryPos, OtherPos),
      ProgramLoc(..) )

import Verifier.SAW.Heapster.Implication
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.TypedCrucible


-- | A single entry in the IDE info dump log.  At a bare minimum, this must
-- include a location and corresponding permission.  Once the basics are
-- working, we can enrich the information we log.
data LogEntryFormat = LogEntryFormat
  { lefLocation :: String
  , lefPermissions :: String
  } deriving (Generic, Show)

instance ToJSON LogEntryFormat
instance NuMatching LogEntryFormat where
  nuMatchingProof = unsafeMbTypeRepr
instance Liftable LogEntryFormat where
  mbLift mb = case mbMatch mb of
    [nuMP| LogEntryFormat x y |] -> LogEntryFormat (mbLift x) (mbLift y)

-- | A complete IDE info dump log, which is just a sequence of entries.  Once
-- the basics are working, we can enrich the information we log.
data LogMainFormat = LogMainFormat {
  lmfEntries :: [LogEntryFormat]
} deriving (Generic, Show)

instance ToJSON LogMainFormat


-- | The entry point for dumping a Heapster environment to a file for IDE
-- consumption.
printIDEInfo :: PermEnv -> [Some SomeTypedCFG] -> FilePath -> IO ()
printIDEInfo _penv tcfgs file = do
  let jsonContent = LogMainFormat $ concatMap handleSomeCFG tcfgs
  encodeFile file jsonContent

-- | This just unwraps the `Some` constructors on a CFG, and then calls out to
-- generate the log entries for it.
handleSomeCFG :: Some SomeTypedCFG -> [LogEntryFormat]
handleSomeCFG cfg =
  case cfg of
    Some (SomeTypedCFG tcfg) ->
      handleBlockMap $ tpcfgBlockMap tcfg

-- | Each TCFG, which is for a function, will have several basic blocks.  This
-- is a map containing those blocks, so we handle each seperately and
-- concatenate the results into one list.
handleBlockMap :: PermCheckExtC ext => TypedBlockMap TransPhase ext blocks tops ret -> [LogEntryFormat]
handleBlockMap bm = do
  concat $ RL.mapToList handleBlock bm

-- | For a single basic block, look at each entry point and dump corresponding information.
handleBlock :: PermCheckExtC ext => TypedBlock TransPhase ext blocks tops ret args -> [LogEntryFormat]
handleBlock tb =
  let tbes = _typedBlockEntries tb
  in concatMap (\case (Some tbe) -> handleTypedEntry' tbe) tbes
   --concatMap handleTypedEntry' tbe

-- handleTypedEntry :: PermCheckExtC ext => TypedEntry ext blocks tops ret args -> String
-- handleTypedEntry (TypedEntry _ _ _ _ _ _ _ perms) =
--   case mbMatch perms of
--     [nuMP| TypedImplStmt permimpl |] -> ""
--     [nuMP| TypedConsStmt loc stmt rets seq |] -> ""
--     [nuMP| TypedTermStmt loc stmt |] -> ""

-- | A single entry point for a particular basic block holds the permissions we
-- want as well as the location information.  For now, since we're only looking
-- at entry permissions, we just take the first location in  the statement
-- sequence and ignore the rest.
handleTypedEntry' :: PermCheckExtC ext => TypedEntry TransPhase ext blocks tops ret args ghosts -> [LogEntryFormat]
handleTypedEntry' te =
  let loc = mbLift $ fmap getFirstProgramLoc (typedEntryBody te)
  in handleMbPerms (typedEntryPermsIn te) loc

-- | From the sequence, get the first program location we encounter, which
-- should correspond to the permissions for the entry point we want to log
getFirstProgramLoc :: PermCheckExtC ext => TypedStmtSeq ext blocks tops ret ctx -> ProgramLoc
getFirstProgramLoc (TypedImplStmt (AnnotPermImpl _ pis)) = getFirstProgramLocPI pis
getFirstProgramLoc (TypedConsStmt loc _ _ _) = loc
getFirstProgramLoc (TypedTermStmt loc _) = loc

getFirstProgramLocPI :: PermCheckExtC ext => PermImpl (TypedStmtSeq ext blocks tops ret) ctx -> ProgramLoc
getFirstProgramLocPI (PermImpl_Done stmts) = getFirstProgramLoc stmts
getFirstProgramLocPI (PermImpl_Step _ mbps) = getFirstProgramLocMBPI mbps

getFirstProgramLocMBPI :: PermCheckExtC ext => MbPermImpls (TypedStmtSeq ext blocks tops ret) ctx -> ProgramLoc
getFirstProgramLocMBPI MbPermImpls_Nil = error "Error finding program location for IDE log"
getFirstProgramLocMBPI (MbPermImpls_Cons _ _ pis) = mbLift $ fmap getFirstProgramLocPI pis

-- | Pretty print the permissions and construct a log entry with the given location.
-- TODO: pattern match on this isntead of mblift
handleMbPerms :: Mb ctx (ValuePerms ctx) -> ProgramLoc -> [LogEntryFormat]
handleMbPerms mbvp loc = mbLift $ fmap handlePerms mbvp
  where
    handlePerms :: ValuePerms ctx -> [LogEntryFormat]
    handlePerms perms = foldValuePerms handlePerm [] perms

    handlePerm :: [LogEntryFormat] -> ValuePerm ctx -> [LogEntryFormat]
    handlePerm rest perm =
      let permStr = permPrettyString emptyPPInfo perm
          (_, locStr) = ppLoc loc
      in LogEntryFormat locStr permStr : rest

-- | Print a `ProgramLoc` in a way that is useful for an IDE, i.e., machine readable
ppLoc :: ProgramLoc -> (String, String)
ppLoc pl =
  let fnName = T.unpack $ functionName $ plFunction pl
      locStr = ppPos $ plSourceLoc pl

      ppPos (SourcePos file line column) = T.unpack file <> ":" <> show line <> ":" <> show column
      ppPos (BinaryPos _ _) = "<unknown binary pos>"
      ppPos (OtherPos _) = "<unknown other pos>"
      ppPos InternalPos = "<unknown internal pos>"
  in (fnName, locStr)
