{
module Verifier.SAW.Heapster.Lexer (lexer) where

import Verifier.SAW.Heapster.Located
import Verifier.SAW.Heapster.Token

}

%wrapper "posn"

$alpha = [a-z A-Z]
$digit = [0-9]

heapster :-

$white+                         ;
"("                             { token_ TOpenParen     }
")"                             { token_ TCloseParen    }
"["                             { token_ TOpenBrack     }
"]"                             { token_ TCloseBrack    }
"{"                             { token_ TOpenBrace     }
"}"                             { token_ TCloseBrace    }
"<"                             { token_ TOpenAngle     }
">"                             { token_ TCloseAngle    }
":"                             { token_ TColon         }
"::"                            { token_ TDoubleColon   }
";"                             { token_ TSemicolon     }
"."                             { token_ TDot           }
","                             { token_ TComma         }
"+"                             { token_ TPlus          }
"*"                             { token_ TStar          }
"@"                             { token_ TAt            }
"-o"                            { token_ TLoli          }
"|->"                           { token_ TMapsTo        }
"=="                            { token_ TEqual         }
"/="                            { token_ TNotEqual      }
"<u"                            { token_ TUnsignedLt    }
"<=u"                           { token_ TUnsignedLe    }
"or"                            { token_ TOr            }
"true"                          { token_ TTrue          }
"empty"                         { token_ TEmpty         }
"exists"                        { token_ TExists        }
"eq"                            { token_ TEq            }
"unit"                          { token_ TUnit          }
"bool"                          { token_ TBool          }
"nat"                           { token_ TNat           }
"bv"                            { token_ TBV            }
"array"                         { token_ TArray         }
"ptr"                           { token_ TPtr           }
"perm"                          { token_ TPerm          }
"llvmptr"                       { token_ TLlvmPtr       }
"llvmfunptr"                    { token_ TLlvmFunPtr    }
"llvmframe"                     { token_ TLlvmFrame     }
"llvmshape"                     { token_ TLlvmShape     }
"llvmblock"                     { token_ TLlvmBlock     }
"llvmword"                      { token_ TLlvmWord      }
"lifetime"                      { token_ TLifetime      }
"lowned"                        { token_ TLOwned        }
"lcurrent"                      { token_ TLCurrent      }
"rwmodality"                    { token_ TRWModality    }
"permlist"                      { token_ TPermList      }
"struct"                        { token_ TStruct        }
"shape"                         { token_ TShape         }
"emptysh"                       { token_ TEmptySh       }
"eqsh"                          { token_ TEqSh          }
"ptrsh"                         { token_ TPtrSh         }
"fieldsh"                       { token_ TFieldSh       }
"arraysh"                       { token_ TArraySh       }
"exsh"                          { token_ TExSh          }
"orsh"                          { token_ TOrSh          }
"memblock"                      { token_ TMemBlock      }
"free"                          { token_ TFree          }
"always"                        { token_ TAlways        }
"R"                             { token_ TR             }
"W"                             { token_ TW             }
$alpha [$alpha $digit _ ']*     { token TIdent          }
$digit+                         { token (TNatLit . read)}
.                               { token TError          }

{

mkPos :: AlexPosn -> Pos
mkPos (AlexPn x y z) = Pos x y z

token :: (String -> Token) -> AlexPosn -> String -> Located Token
token tok p str = Located (mkPos p) (tok str)

token_ :: Token -> AlexPosn -> String -> Located Token
token_ tok p _ = Located (mkPos p) tok

lexer :: String -> [Located Token]
lexer = alexScanTokens

}
