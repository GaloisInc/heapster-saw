{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Heapster.IDESupport where

import Data.Aeson
import Data.Binding.Hobbits (Mb(..), Liftable, NuMatching, mbLift, mkNuMatching, mbMatch, nuMP)
import Data.Parameterized.Some (Some (..))
import qualified Data.Type.RList as RL
import GHC.Generics
import Lang.Crucible.LLVM.MemModel (GlobalSymbol (..))
import System.IO (hPutStr, withFile, IOMode(..))
import Text.LLVM.AST (Symbol (..))


import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.TypedCrucible

data LogFileFormat = LogFileFormat 
  { filename :: String
  , directory :: String
  } deriving (Generic, Show)

instance ToJSON LogFileFormat
instance NuMatching LogFileFormat
instance Liftable LogFileFormat where
  mbLift mb = case mbMatch mb of
    [nuMP| LogFileFormat x y |] -> LogFileFormat (mbLift x) (mbLift y)

data LogPermissionsFormat = LogPermissionsFormat
  { line :: Int
  , permission :: String
  } deriving (Generic, Show)

instance ToJSON LogPermissionsFormat
instance NuMatching LogPermissionsFormat
instance Liftable LogPermissionsFormat where
  mbLift mb = case mbMatch mb of
    [nuMP| LogPermissionsFormat x y |] -> LogPermissionsFormat (mbLift x) (mbLift y)


data LogEntryFormat = LogEntryFormat 
  { name :: String
  , file :: LogFileFormat
  , permissions :: [LogPermissionsFormat]
  } deriving (Generic, Show)

instance ToJSON LogEntryFormat
instance NuMatching LogEntryFormat
instance Liftable LogEntryFormat where
  mbLift mb = case mbMatch mb of
    [nuMP| LogEntryFormat x y z |] -> LogEntryFormat (mbLift x) (mbLift y) (mbLift z)

data LogMainFormat = LogMainFormat {
  function :: [LogEntryFormat]
} deriving (Generic, Show)

instance ToJSON LogMainFormat


printIDEInfo :: String -> PermEnv -> [Some SomeTypedCFG] -> IO ()
printIDEInfo fnName henv tcfgs = do
  mapM_ handleSomeCFG tcfgs

handleSomeCFG :: Some SomeTypedCFG -> IO ()
handleSomeCFG cfg =
  case cfg of
    Some (SomeTypedCFG tcfg) ->
      handleBlockMap $ tpcfgBlockMap tcfg


handleBlockMap :: PermCheckExtC ext => TypedBlockMap ext blocks tops ret -> IO ()
handleBlockMap bm = do
  let json = LogMainFormat $ concat $ RL.mapToList handleBlock bm
  encodeFile "karl" json
  
handleBlock :: PermCheckExtC ext => TypedBlock ext blocks tops ret args -> [LogEntryFormat]
handleBlock tb = 
  concatMap handleTypedEntry' (typedBlockEntries tb)
  -- concatMap handleTypedEntry' (typedBlockEntries tb) <> ", " <> str

-- handleTypedEntry :: PermCheckExtC ext => TypedEntry ext blocks tops ret args -> String
-- handleTypedEntry (TypedEntry _ _ _ _ _ _ _ perms) =
--   case mbMatch perms of
--     [nuMP| TypedImplStmt permimpl |] -> ""
--     [nuMP| TypedConsStmt loc stmt rets seq |] -> ""
--     [nuMP| TypedTermStmt loc stmt |] -> ""

handleTypedEntry' :: PermCheckExtC ext => TypedEntry ext blocks tops ret args -> [LogEntryFormat]
handleTypedEntry' (TypedEntry _ _ _ _ _ perms _ _) = 
  handlePerms perms

handlePerms :: Mb ctx (ValuePerms ctx) -> [LogEntryFormat]
handlePerms mbvp = mbLift $ fmap handlePerms mbvp
  where
    handlePerms :: ValuePerms ctx -> [LogEntryFormat]
    handlePerms perms = foldValuePerms handlePerm [] perms

    handlePerm :: [LogEntryFormat] -> ValuePerm ctx -> [LogEntryFormat]
    handlePerm rest perm = 
      let str = permPrettyString emptyPPInfo perm
      in LogEntryFormat "name" (LogFileFormat "filename" "dir") [LogPermissionsFormat 1 str] : rest
-- handlePerm rest (ValPerm_Eq pe) =  "valperm_eq " <> rest
-- handlePerm rest (ValPerm_Or _ _) = "valperm_or " <> rest
-- handlePerm rest (ValPerm_Exists _) = "valperm_exists " <> rest
-- handlePerm rest (ValPerm_Named _ _ _) = "valperm_named " <> rest
-- handlePerm rest (ValPerm_Var _ _) = "valperm_var " <> rest
-- handlePerm rest (ValPerm_Conj _) = "valperm_conj " <> rest

handlePermExpr :: PermExpr a -> String
handlePermExpr = permPrettyString emptyPPInfo

-- data TypedStmtSeq ext blocks tops ret ps_in where
--   -- | A permission implication step, which modifies the current permission
--   -- set. This can include pattern-matches and/or assertion failures.
--   TypedImplStmt :: !(AnnotPermImpl (TypedStmtSeq ext blocks tops ret) ps_in) ->
--                    TypedStmtSeq ext blocks tops ret ps_in

--   -- | Typed version of 'ConsStmt', which binds new variables for the return
--   -- value(s) of each statement
--   TypedConsStmt :: !ProgramLoc ->
--                    !(TypedStmt ext rets ps_in ps_next) ->
--                    !(RAssign Proxy rets) ->
--                    !(Mb rets (TypedStmtSeq ext blocks tops ret ps_next)) ->
--                    TypedStmtSeq ext blocks tops ret ps_in

--   -- | Typed version of 'TermStmt', which terminates the current block
--   TypedTermStmt :: !ProgramLoc ->
--                    !(TypedTermStmt blocks tops ret ps_in) ->
--                    TypedStmtSeq ext blocks tops ret ps_in

-- dumpPerms :: Mb 


  -- data TypedEntry ext blocks tops ret args where
  -- TypedEntry ::
  --   !(TypedEntryID blocks args ghosts) ->
  --   !(TypedEntryInDegree) ->
  --   !(CruCtx tops) -> !(CruCtx args) -> !(TypeRepr ret) ->
  --   !(MbValuePerms ((tops :++: args) :++: ghosts)) ->
  --   !(Mb ((tops :++: args) :++: ghosts :> ret) (ValuePerms (tops :> ret))) ->
  --   !(Mb ((tops :++: args) :++: ghosts)
  --     (TypedStmtSeq ext blocks tops ret ((tops :++: args) :++: ghosts))) ->
  --   TypedEntry ext blocks tops ret args