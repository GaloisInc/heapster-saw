{-# Language ImportQualifiedPost #-}
{-# Language ScopedTypeVariables #-}
{-# Language GADTs #-}
{-# Language TypeOperators #-}
module Verifier.SAW.Heapster.ParsedCtx where

import Data.Functor.Constant

import Data.Binding.Hobbits

import Data.Type.RList qualified as RL

import Data.Parameterized.Some (Some(Some))

import Lang.Crucible.Types

import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.CruUtil

-- | A sequence of variable names and their types
data ParsedCtx ctx = ParsedCtx {
  parsedCtxNames :: RAssign (Constant String) ctx,
  parsedCtxCtx :: CruCtx ctx
  }

-- | Remove the last variable in a 'ParsedCtx'
parsedCtxUncons :: ParsedCtx (ctx :> tp) -> ParsedCtx ctx
parsedCtxUncons (ParsedCtx (xs :>: _) (CruCtxCons ctx _)) = ParsedCtx xs ctx

-- | Add a variable name and type to a 'ParsedCtx'
consParsedCtx :: String -> TypeRepr tp -> ParsedCtx ctx ->
                 ParsedCtx (ctx :> tp)
consParsedCtx x tp (ParsedCtx xs ctx) =
  ParsedCtx (xs :>: Constant x) (CruCtxCons ctx tp)

-- | An empty 'ParsedCtx'
emptyParsedCtx :: ParsedCtx RNil
emptyParsedCtx = ParsedCtx MNil CruCtxNil

-- | Append two 'ParsedCtx's
appendParsedCtx :: ParsedCtx ctx1 -> ParsedCtx ctx2 ->
                   ParsedCtx (ctx1 :++: ctx2)
appendParsedCtx (ParsedCtx ns1 ctx1) (ParsedCtx ns2 ctx2) =
  ParsedCtx (RL.append ns1 ns2) (appendCruCtx ctx1 ctx2)

-- | Add a variable name and type to the beginning of an unknown 'ParsedCtx'
preconsSomeParsedCtx :: String -> Some TypeRepr -> Some ParsedCtx ->
                        Some ParsedCtx
preconsSomeParsedCtx x (Some (tp :: TypeRepr tp)) (Some (ParsedCtx ns tps)) =
  Some $ ParsedCtx
  (RL.append (MNil :>: (Constant x :: Constant String tp)) ns)
  (appendCruCtx (singletonCruCtx tp) tps)

-- | Make a 'ParsedCtx' where the string names are @"arg0,arg1,..."@
mkArgsParsedCtx :: CruCtx ctx -> ParsedCtx ctx
mkArgsParsedCtx ctx = ParsedCtx (mkArgsParsedCtx' ctx) ctx

mkArgsParsedCtx' :: CruCtx ctx -> RAssign (Constant String) ctx
mkArgsParsedCtx' CruCtxNil = MNil
mkArgsParsedCtx' (CruCtxCons ctx _) =
  mkArgsParsedCtx' ctx :>: Constant ("arg" ++ show (cruCtxLen ctx))

-- | Change the type of the last element of a 'ParsedCtx'
parsedCtxSetLastType :: TypeRepr tp -> ParsedCtx (ctx :> tp') ->
                        ParsedCtx (ctx :> tp)
parsedCtxSetLastType tp (ParsedCtx (xs :>: Constant str) (CruCtxCons ctx _)) =
  (ParsedCtx (xs :>: Constant str) (CruCtxCons ctx tp))

-- | Extract out the last element of a 'ParsedCtx' as a singleton 'ParsedCtx'
parsedCtxLast :: ParsedCtx (ctx :> tp) -> ParsedCtx (RNil :> tp)
parsedCtxLast (ParsedCtx (_ :>: Constant str) (CruCtxCons _ tp)) =
  ParsedCtx (MNil :>: Constant str) (CruCtxCons CruCtxNil tp)
