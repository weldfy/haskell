{
{-# LANGUAGE LambdaCase #-}
module Parser where
import Tokenizer
}

%name         parse
%tokentype    { StatToken }
%error        { error "ZALUPA" }

%token
  LEFT        {ST_LPAR}
  RIGHT        {ST_RPAR}
  NEXT        {ST_Next}
  POINT        {ST_Point}
  NOT        {ST_Not}
  OR        {ST_Or}
  AND        {ST_And}
  IMPL        {ST_Con}
  ALL        {ST_All}
  ONE        {ST_One}
  VAR        {ST_Var $$}
  PRED       {ST_Pred $$}
%%

Expr:
  Or {$1}
  | Or IMPL Expr {SE_Con $1 $3}

Or:
  And {$1}
  | Or OR And {SE_Or $1 $3}

And:
  Unar {$1}
  | And AND Unar {SE_And $1 $3}

Unar:
  NOT Unar {SE_Not $2}
  | LEFT Expr RIGHT {$2}
  | ALL VAR POINT Expr {SE_All $2 $4}
  | ONE VAR POINT Expr {SE_One $2 $4}
  | Pred {$1}

Pred:
  PRED LEFT Args RIGHT {SE_Pred $1 $3}
  | PRED LEFT RIGHT {SE_Pred $1 SE_LastArg}
  | PRED {SE_Pred $1 SE_LastArg}

Args:
  Term NEXT Args {SE_Args $1 $3}
  | Term {SE_Args $1 SE_LastArg}

Term:
  LEFT Term RIGHT {$2}
  | VAR LEFT Args RIGHT {SE_Func $1 $3}
  | VAR LEFT RIGHT {SE_Func $1 SE_LastArg}
  | VAR {SE_Var $1}

{
data StatExpr
  = SE_Func String StatExpr
  | SE_Var String
  | SE_Args StatExpr StatExpr
  | SE_LastArg
  | SE_Pred String StatExpr
  | SE_Not StatExpr
  | SE_And StatExpr StatExpr
  | SE_Or StatExpr StatExpr
  | SE_Con StatExpr StatExpr
  | SE_All String StatExpr
  | SE_One String StatExpr
  | SE_Null
  deriving (Eq)

instance Show StatExpr where
  show = \case
    SE_Func x exp -> x ++ "(" ++ show exp ++ ")"
    SE_Pred x exp -> x ++ "(" ++ show exp ++ ")"
    SE_Var x -> x
    SE_Args exp SE_LastArg -> show exp
    SE_Args exp next -> show exp ++ "," ++ show next
    SE_LastArg -> ""
    SE_Not exp -> "!(" ++ show exp ++ ")"
    SE_And a b -> "(" ++ show a ++ "&" ++ show b ++ ")"
    SE_Or a b -> "(" ++ show a ++ "|" ++ show b ++ ")"
    SE_Con a b -> "(" ++ show a ++ "->" ++ show b ++ ")"
    SE_All x exp -> "(@" ++ x ++ ".(" ++ show exp ++ "))"
    SE_One x exp -> "(?" ++ x ++ ".(" ++ show exp ++ "))"
    SE_Null -> "ZALUPA"
}
