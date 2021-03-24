{
{-# Language ViewPatterns #-}
module Verifier.SAW.Heapster.Parser where

import GHC.Natural

import Verifier.SAW.Heapster.Located
import Verifier.SAW.Heapster.Token
import Verifier.SAW.Heapster.UntypedAST

}

%tokentype      { Located Token                         }
%token
'('             { Located $$ TOpenParen                 }
')'             { Located $$ TCloseParen                }
'['             { Located $$ TOpenBrack                 }
']'             { Located $$ TCloseBrack                }
'{'             { Located $$ TOpenBrace                 }
'}'             { Located $$ TCloseBrace                }
'<'             { Located $$ TOpenAngle                 }
'>'             { Located $$ TCloseAngle                }
':'             { Located $$ TColon                     }
'::'            { Located $$ TDoubleColon               }
';'             { Located $$ TSemicolon                 }
'.'             { Located $$ TDot                       }
','             { Located $$ TComma                     }
'+'             { Located $$ TPlus                      }
'*'             { Located $$ TStar                      }
'@'             { Located $$ TAt                        }
'-o'            { Located $$ TLoli                      }
'|->'           { Located $$ TMapsTo                    }
'=='            { Located $$ TEqual                     }
'/='            { Located $$ TNotEqual                  }
'<u'            { Located $$ TUnsignedLt                }
'<=u'           { Located $$ TUnsignedLe                }
'or'            { Located $$ TOr                        }
'true'          { Located $$ TTrue                      }
'empty'         { Located $$ TEmpty                     }
'exists'        { Located $$ TExists                    }
'eq'            { Located $$ TEq                        }
'unit'          { Located $$ TUnit                      }
'bool'          { Located $$ TBool                      }
'nat'           { Located $$ TNat                       }
'bv'            { Located $$ TBV                        }
'array'         { Located $$ TArray                     }
'ptr'           { Located $$ TPtr                       }
'perm'          { Located $$ TPerm                      }
'llvmptr'       { Located $$ TLlvmPtr                   }
'llvmfunptr'    { Located $$ TLlvmFunPtr                }
'llvmframe'     { Located $$ TLlvmFrame                 }
'llvmshape'     { Located $$ TLlvmShape                 }
'llvmblock'     { Located $$ TLlvmBlock                 }
'llvmword'      { Located $$ TLlvmWord                  }
'lifetime'      { Located $$ TLifetime                  }
'lowned'        { Located $$ TLOwned                    }
'lcurrent'      { Located $$ TLCurrent                  }
'rwmodality'    { Located $$ TRWModality                }
'permlist'      { Located $$ TPermList                  }
'struct'        { Located $$ TStruct                    }
'shape'         { Located $$ TShape                     }
'emptysh'       { Located $$ TEmptySh                   }
'eqsh'          { Located $$ TEqSh                      }
'ptrsh'         { Located $$ TPtrSh                     }
'fieldsh'       { Located $$ TFieldSh                   }
'arraysh'       { Located $$ TArraySh                   }
'exsh'          { Located $$ TExSh                      }
'orsh'          { Located $$ TOrSh                      }
'memblock'      { Located $$ TMemBlock                  }
'free'          { Located $$ TFree                      }
'always'        { Located $$ TAlways                    }
'R'             { Located $$ TR                         }
'W'             { Located $$ TW                         }
IDENT           { (traverse tokenIdent -> Just $$)      }
NAT             { (traverse tokenNat   -> Just $$)      }


%monad          { Either (Located Token)                }
%error          { errorP                                }

%name parseCtx          ctx
%name parseType         astType
%name parseFunPerm      funPerm
%name parseAstExpr      astExpr

%right    '.'
%left     'orsh'
%left     ';'
%left     'or'
%nonassoc '==' '/=' '<u' '<=u'
%left     '+'
%left     '*'

%%

ctx ::                                          {[(String, AstType)]}
  : list(varType)                               { $1 }

astType ::                                      { AstType }
  : '(' astType ')'                             { $2 }
  | 'unit'                                      { TyUnit (pos $1) }
  | 'bool'                                      { TyBool (pos $1) }
  | 'nat'                                       { TyNat (pos $1) }
  | 'lifetime'                                  { TyLifetime (pos $1) }
  | 'rwmodality'                                { TyRwModality (pos $1) }
  | 'permlist'                                  { TyPermList (pos $1) }
  | 'bv'        NAT                             { TyBV        (pos $1) (locThing $2) }
  | 'llvmptr'   NAT                             { TyLlvmPtr   (pos $1) (locThing $2) }
  | 'llvmframe' NAT                             { TyLlvmFrame (pos $1) (locThing $2) }
  | 'llvmblock' NAT                             { TyLlvmBlock (pos $1) (locThing $2) }
  | 'llvmshape' NAT                             { TyLlvmShape (pos $1) (locThing $2) }
  | 'struct' '(' list(astType) ')'              { TyStruct (pos $1) $3 }
  | 'perm'   '(' astType      ')'               { TyPerm (pos $1) $3 }

astExpr ::                                      { AstExpr }
  : '(' astExpr ')'                             { $2 }
  | 'always'                                    { ExAlways (pos $1) }
  | 'unit'                                      { ExUnit (pos $1) }
  | NAT                                         { ExNat (pos $1) (locThing $1) }
  | astExpr '+' astExpr                         { ExAdd (pos $2) $1 $3 }
  | astExpr '*' astExpr                         { ExMul (pos $2) $1 $3 }
  | 'R'                                         { ExRead (pos $1) }
  | 'W'                                         { ExWrite (pos $1) }
  | 'struct' '(' list(astExpr) ')'              { ExStruct (pos $1) $3 }
  | 'llvmword' '(' astExpr ')'                  { ExLlvmWord (pos $1) $3 }

  | 'emptysh'                                   { ExEmptySh (pos $1) }
  | 'eqsh' '(' astExpr ')'                      { ExEqSh (pos $1) $3 }

  | lifetimePrefix 'ptrsh' '(' astExpr ',' astExpr ')'
                                                { ExPtrSh (pos $2) $1 (Just $4) $6 }
  | lifetimePrefix 'ptrsh' '(' astExpr ')'      { ExPtrSh (pos $2) $1 Nothing $4 }

  | 'fieldsh' '(' astExpr ',' astExpr ')'       { ExFieldSh (pos $1) (Just $3) $5 }
  | 'fieldsh' '('             astExpr ')'       { ExFieldSh (pos $1) Nothing $3 }
  | 'arraysh' '(' astExpr ',' astExpr ',' '[' list(shape) ']' ')'
                                                { ExArraySh (pos $1) $3 $5 $8 }
  | 'exsh' IDENT ':' astType '.' astExpr        { ExExSh (pos $1) (locThing $2) $4 $6 }
  | astExpr 'orsh' astExpr                      { ExOrSh (pos $2) $1 $3 }
  | astExpr ';' astExpr                         { ExSeqSh (pos $2) $1 $3 }

  | 'true'                                      { ExTrue (pos $1) }
  | astExpr 'or' astExpr                        { ExOr (pos $2) $1 $3 }

  | 'eq' '(' astExpr ')'                        { ExEq (pos $1) $3 }
  | 'exists' IDENT ':' astType '.' astExpr      { ExExists (pos $1) (locThing $2) $4 $6 }
  | IDENT identArgs permOffset                  { ExVar (pos $1) (locThing $1) $2 $3 }

  | 'array' '(' astExpr ',' '<' astExpr ',' '*' astExpr ',' '[' list(llvmFieldPermArray) ']' ')'
                                                { ExArray (pos $1) $3 $6 $9 $12 }
  | lifetimePrefix 'memblock' '(' astExpr ',' astExpr ',' astExpr ',' astExpr ')'
                                                { ExMemblock (pos $2) $1 $4 $6 $8 $10 }
  | 'free' '(' astExpr ')'                      { ExFree (pos $1) $3 }
  | 'llvmfunptr' '{' astExpr ',' astExpr '}' '(' funPerm ')'
                                                { ExLlvmFunPtr (pos $1) $3 $5 $8 }
  | 'llvmframe' '[' list(frameEntry) ']'        { ExLlvmFrame (pos $1) $3 }
  | lifetimePrefix 'ptr' '(' '(' astExpr ',' astExpr ',' astExpr ')' '|->' astExpr ')'
                                                { ExPtr (pos $2) $1 $5 $7 (Just $9) $12 }
  | lifetimePrefix 'ptr' '(' '(' astExpr ',' astExpr             ')' '|->' astExpr ')'
                                                { ExPtr (pos $2) $1 $5 $7 Nothing $10 }

  | 'shape' '(' astExpr ')'                     { ExShape (pos $1) $3}
  | 'lowned' '(' list(varExpr) '-o' list1(varExpr) ')'
                                                { ExLOwned (pos $1) $3 $5}
  | lifetimePrefix 'lcurrent'                   { ExLCurrent (pos $2) $1 }

  | astExpr '=='  astExpr                       { ExEqual (pos $2) $1 $3}
  | astExpr '/='  astExpr                       { ExNotEqual (pos $2) $1 $3}
  | astExpr '<u'  astExpr                       { ExLessThan (pos $2) $1 $3}
  | astExpr '<=u' astExpr                       { ExLessEqual (pos $2) $1 $3}

frameEntry ::                                   { (AstExpr, Natural) }
  : astExpr ':' NAT                             { ($1, locThing $3) }

shape ::                                        { (Maybe AstExpr, AstExpr) }
  :  astExpr                                    { (Nothing, $1)         }
  |  '(' astExpr ',' astExpr ')'                { (Just $2, $4)         }

identArgs ::                                    { Maybe [AstExpr]       }
  :                                             { Nothing               }
  | '<' list(astExpr) '>'                       { Just $2               }

permOffset ::                                   { Maybe AstExpr         }
  :                                             { Nothing               }
  | '@' '(' astExpr ')'                         { Just $3               }
  | '@' NAT                                     { Just (ExNat (pos $2) (locThing $2)) }
  | '@' IDENT                                   { Just (ExVar (pos $2) (locThing $2) Nothing Nothing) }

funPerm ::                                      { AstFunPerm }
  : '(' ctx ')' '.' funPermList '-o' funPermList
                                                { AstFunPerm (pos $6) $2 $5 $7 }

funPermList ::                                  { [(String, AstExpr)]   }
  : 'empty'                                     { []                    }
  | list1(varExpr)                              { $1                    }

varExpr ::                                      { (String, AstExpr)     }
  : IDENT ':' astExpr                           { (locThing $1, $3)     }

varType ::                                      { (String, AstType)     }
  : IDENT ':' astType                           { (locThing $1, $3)     }

lifetimePrefix ::                               { Maybe AstExpr         }
  : '[' astExpr ']'                             { Just $2               }
  |                                             { Nothing               }

llvmFieldPermArray ::                           { ArrayPerm             }
  : lifetimePrefix '(' astExpr ',' astExpr ',' astExpr ')' '|->' astExpr
                                                { ArrayPerm (pos $9) $1 $3 $5 (Just $7) $10 }
  | lifetimePrefix '(' astExpr ',' astExpr             ')' '|->' astExpr
                                                { ArrayPerm (pos $7) $1 $3 $5 Nothing $8 }

list(p) ::                                      { [p]                   }
  :                                             { []                    }
  | list1(p)                                    { $1                    }

list1(p) ::                                     { [p]                   }
  : list1R(p)                                   { reverse $1            }

list1R(p) ::                                    { [p]                   }
  :               p                             { [$1]                  }
  | list1R(p) ',' p                             { $3 : $1               }

{
errorP :: [Located Token] -> Either (Located Token) a
errorP (t:_) = Left t
errorP _ = error "Unexpected end of file" -- XXX
}
