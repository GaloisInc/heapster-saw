{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}

module Verifier.SAW.Heapster.IDESupport where

import qualified Data.Binding.Hobbits
import Data.Parameterized.Some (Some (..))
import qualified Data.Type.RList as RL
import Lang.Crucible.LLVM.MemModel (GlobalSymbol (..))
import Text.LLVM.AST (Symbol (..))
import Verifier.SAW.Heapster.Permissions (PermEnv (..), PermEnvGlobalEntry (..), permPrettyString, PermEnvFunEntry (PermEnvFunEntry))
import Verifier.SAW.Heapster.TypedCrucible

printIDEInfo :: String -> PermEnv -> [SomeTypedCFG] -> IO ()
printIDEInfo fnName henv tcfgs = do
  -- mapM_ ((\fun -> case fun of
  --                  (PermEnvFunEntry handle perms ident) -> do
  --                    putStrLn "hello"
  --       ) :: PermEnvFunEntry -> IO ()) (permEnvFunPerms penv)


  let handleSomeCFG :: SomeTypedCFG -> IO ()
      handleSomeCFG cfg =
        case cfg of
          (SomeTypedCFG tcfg) ->
            handleBlockMap $ tpcfgBlockMap tcfg





            -- case mbMatch (tpcfgBlockMap tcfg) of
            --   [nuMP| MNil |] -> return ()
            --   [nuMP| rest :>: b|] -> return ()

  return ()

  -- genSubst s mb_x = case mbMatch mb_x of
  --   [nuMP| RegWithVal r e |] ->
  --     RegWithVal <$> genSubst s r <*> genSubst s e
  --   [nuMP| RegNoVal r |] -> RegNoVal <$> genSubst s r
            -- MNil -> undefined
            -- rest :>: f -> undefined



      --let _ = mapRAssign (\tb ->
                --let es = typedBlockEntries tb
                    --es' = map (\(TypedEntry _ _ _ _ _ _ _ stmts) ->
                                  --dumpErrors stmts
                              --) es
                --in es'
                --) $ tpcfgBlockMap tcfg
  -- where
    -- symbolNameMatches :: String -> PermEnvGlobalEntry -> Bool
    -- symbolNameMatches fn (PermEnvGlobalEntry (GlobalSymbol (Symbol nm)) _ _) =
    --   fn == nm

    -- dumpErrors [nuP| [TypedImplStmt api] |] = "test"
    -- dumpErrors _ = "fail"

handleBlockMap :: TypedBlockMap ext blocks tops ret -> IO ()
handleBlockMap bm = do
  let str = RL.foldr handleBlock "" bm
  return ()

handleBlock :: TypedBlock ext blocks tops ret args -> String -> String
handleBlock tb str =
  let tes = typedBlockEntries tb
  in concatMap handleEntry tes ++ str

handleEntry :: TypedEntry ext blocks tops ret args -> String
handleEntry (TypedEntry _ _ _ _ _ perms _ _) =
  undefined
  -- map dumpPerms perms

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