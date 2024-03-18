{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main (main) where

import Control.Applicative
import Data.Char
import GHC.List
import Prelude hiding (exp)

main :: IO ()
main = do
  z <- getLine
  solve (delJust (parseks z))

solve :: StatExpr -> IO ()
solve exp = do
  let names = getNames exp
  let correct = checkCorrect (Prelude.length names) names [] exp
  if correct /= Nothing
    then putStrLn (delJust correct)
    else buildTree 0 exp names [] []

  where
    buildTree :: Int -> StatExpr -> [String] -> [String] -> [Bool] -> IO ()
    buildTree level exp [] names vals = calcTree level exp names vals ""
    buildTree level exp (name : rect) names vals = do
      buildTree (level + 1) exp rect (name : names) (True : vals)
      buildTree (level + 1) exp rect (name : names) (False : vals)
      delName (level + 1) name names vals
      putStrLn ("[" ++ show level ++ "] " ++ printGips names vals ++ "|-" ++ show exp ++ " [E|]")

    calcTree :: Int -> StatExpr -> [String] -> [Bool] -> String -> IO ()
    calcTree level (SE_Var x) names vals texgips = do
      let val = podzalupik x names vals
      let gips = printGips names vals ++ if texgips /= "" && names /= [] then "," ++ texgips else texgips
      if val
        then putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-" ++ show (SE_Var x) ++ " [Ax]")
        else putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-" ++ show (SE_Var x) ++ "->_|_ [Ax]")

    calcTree level SE_Not names vals texgips = do
      let gips = printGips names vals ++ if texgips /= "" && names /= [] then "," ++ texgips else texgips
          gips' = if gips == "" then gips else gips ++ ","
      putStrLn ("[" ++ show (level + 4) ++ "] " ++ gips' ++ "_|_,_|_,_|_->_|_|-_|_ [Ax]")
      putStrLn ("[" ++ show (level + 3) ++ "] " ++ gips' ++ "_|_,_|_->_|_|-_|_->_|_ [I->]")
      putStrLn ("[" ++ show (level + 3) ++ "] " ++ gips' ++ "_|_,_|_->_|_|-_|_ [Ax]")
      putStrLn ("[" ++ show (level + 2) ++ "] " ++ gips' ++ "_|_,_|_->_|_|-_|_ [E->]")
      putStrLn ("[" ++ show (level + 1) ++ "] " ++ gips' ++ "_|_|-_|_ [E!!]")
      putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-_|_->_|_ [I->]")

    calcTree level (SE_And a b) names vals texgips = do
      let l = evalExpr a names vals
          r = evalExpr b names vals
          gips = printGips names vals ++ if texgips /= "" && names /= [] then "," ++ texgips else texgips
          gips' = if gips == "" then gips else gips ++ "," 
      if l
        then if r
          then do
            calcTree (level + 1) a names vals texgips
            calcTree (level + 1) b names vals texgips
            putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-" ++ show (SE_And a b) ++ " [I&]")
          else do
            calcTree (level + 2) b names vals (texgips ++ if texgips == "" then show a ++ "&" ++ show b else "," ++ show a ++ "&" ++ show b)
            putStrLn ("[" ++ show (level + 3) ++ "] " ++ gips' ++ show a ++ "&" ++ show b ++ "|-" ++ show a ++ "&" ++ show b ++ " [Ax]")
            putStrLn ("[" ++ show (level + 2) ++ "] " ++ gips' ++ show a ++ "&" ++ show b ++ "|-" ++ show b ++ " [Er&]")
            putStrLn ("[" ++ show (level + 1) ++ "] " ++ gips' ++ show a ++ "&" ++ show b ++ "|-_|_ [E->]")
            putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-" ++ show a ++ "&" ++ show b ++ "->_|_ [I->]")
        else do
          calcTree (level + 2) a names vals (texgips ++ if texgips == "" then show a ++ "&" ++ show b else "," ++ show a ++ "&" ++ show b)
          putStrLn ("[" ++ show (level + 3) ++ "] " ++ gips' ++ show a ++ "&" ++ show b ++ "|-" ++ show a ++ "&" ++ show b ++ " [Ax]")
          putStrLn ("[" ++ show (level + 2) ++ "] " ++ gips' ++ show a ++ "&" ++ show b ++ "|-" ++ show a ++ " [El&]")
          putStrLn ("[" ++ show (level + 1) ++ "] " ++ gips' ++ show a ++ "&" ++ show b ++ "|-_|_ [E->]")
          putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-" ++ show a ++ "&" ++ show b ++ "->_|_ [I->]")

    calcTree level (SE_Or a b) names vals texgips = do
      let l = evalExpr a names vals
          r = evalExpr b names vals
          gips = printGips names vals ++ if texgips /= "" && names /= [] then "," ++ texgips else texgips
          gips' = if gips == "" then gips else gips ++ "," 
      if l
        then do
          calcTree (level + 1) a names vals texgips
          putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-" ++ show a ++ "|" ++ show b ++ " [Il|]")
        else if r
          then do
            calcTree (level + 1) b names vals texgips
            putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-" ++ show a ++ "|" ++ show b ++ " [Ir|]")
          else do
            calcTree (level + 3) a names vals (texgips ++ if texgips == "" then show a ++ "," ++ show a ++ "|" ++ show b else "," ++ show a ++ "," ++ show a ++ "|" ++ show b)
            putStrLn("[" ++ show (level + 3) ++ "] " ++ gips' ++ show a ++ "," ++ show a ++ "|" ++ show b ++ "|-" ++ show a ++ " [Ax]")
            putStrLn("[" ++ show (level + 2) ++ "] " ++ gips' ++ show a ++ "," ++ show a ++ "|" ++ show b ++ "|-_|_ [E->]")
            calcTree (level + 3) b names vals (texgips ++ if texgips == "" then show b ++ "," ++ show a ++ "|" ++ show b else "," ++ show b ++ "," ++ show a ++ "|" ++ show b)
            putStrLn("[" ++ show (level + 3) ++ "] " ++ gips' ++ show b ++ "," ++ show a ++ "|" ++ show b ++ "|-" ++ show b ++ " [Ax]")
            putStrLn("[" ++ show (level + 2) ++ "] " ++ gips' ++ show b ++ "," ++ show a ++ "|" ++ show b ++ "|-_|_ [E->]")
            putStrLn("[" ++ show (level + 2) ++ "] " ++ gips' ++ show a ++ "|" ++ show b ++ "|-" ++ show a ++ "|" ++ show b ++ " [Ax]")
            putStrLn("[" ++ show (level + 1) ++ "] " ++ gips' ++ show a ++ "|" ++ show b ++ "|-_|_ [E|]")
            putStrLn("[" ++ show level ++ "] " ++ gips ++ "|-" ++ show a ++ "|" ++ show b ++ "->_|_ [I->]")

    calcTree level (SE_Con a b) names vals texgips = do
      let l = evalExpr a names vals
          r = evalExpr b names vals
          gips = printGips names vals ++ if texgips /= "" && names /= [] then "," ++ texgips else texgips
          gips' = if gips == "" then gips else gips ++ ","
      if l
        then if r
          then do
            calcTree (level + 1) b names vals (texgips ++ if texgips == "" then show a else "," ++ show a)
            putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-" ++ show a ++ "->" ++ show b ++ " [I->]")
          else do
            calcTree (level + 2) b names vals (texgips ++ if texgips == "" then show a ++ "->" ++ show b else "," ++ show a ++ "->" ++ show b)
            putStrLn ("[" ++ show (level + 3) ++ "] " ++ gips' ++ show a ++ "->" ++ show b ++ "|-" ++ show a ++ "->" ++ show b ++ " [Ax]")
            calcTree (level + 3) a names vals (texgips ++ if texgips == "" then show a ++ "->" ++ show b else "," ++ show a ++ "->" ++ show b)
            putStrLn ("[" ++ show (level + 2) ++ "] " ++ gips' ++ show a ++ "->" ++ show b ++ "|-" ++ show b ++ " [E->]")
            putStrLn ("[" ++ show (level + 1) ++ "] " ++ gips' ++ show a ++ "->" ++ show b ++ "|-_|_ [E->]")
            putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-(" ++ show a ++ "->" ++ show b ++ ")->_|_ [I->]")
        else if r
          then do
            calcTree (level + 1) b names vals (texgips ++ if texgips == "" then show a else "," ++ show a)
            putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-" ++ show a ++ "->" ++ show b ++ " [I->]")
          else do
            calcTree (level + 3) a names vals (texgips ++ if texgips == "" then show a ++ "," ++ show b ++ "->_|_" else "," ++ show a ++ "," ++ show b ++ "->_|_")
            putStrLn ("[" ++ show (level + 3) ++ "] " ++ gips' ++ show a ++ "," ++ show b ++ "->_|_|-" ++ show a ++ " [Ax]")
            putStrLn ("[" ++ show (level + 2) ++ "] " ++ gips' ++ show a ++ "," ++ show b ++ "->_|_|-_|_ [E->]")
            putStrLn ("[" ++ show (level + 1) ++ "] " ++ gips' ++ show a ++ "|-" ++ show b ++ " [E!!]")
            putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-" ++ show a ++ "->" ++ show b ++ " [I->]")

    printGips :: [String] -> [Bool] -> String
    printGips [] [] = ""
    printGips [name] [x]
      | x = name
      | otherwise = name ++ "->_|_"
    printGips (name : rect1) (x : rect2)
      | x = name ++ "," ++ printGips rect1 rect2 
      | otherwise = name ++ "->_|_," ++ printGips rect1 rect2
    
    delName :: Int -> String -> [String] -> [Bool] -> IO ()
    delName level name names vals = do
      let gips = printGips names vals
          gips' = if gips == "" then gips else "," ++ gips
      putStrLn ("[" ++ show (level + 2) ++ "] " ++ name ++ "|(" ++ name ++ "->_|_)->_|_" ++ gips' ++ "|-" ++ name ++ "|(" ++ name ++ "->_|_)->_|_ [Ax]")
      putStrLn ("[" ++ show (level + 5) ++ "] " ++ name ++ "," ++ name ++ "|(" ++ name ++ "->_|_)->_|_" ++ gips' ++ "|-" ++ name ++ "|(" ++ name ++ "->_|_)->_|_ [Ax]")
      putStrLn ("[" ++ show (level + 6) ++ "] " ++ name ++ "," ++ name ++ "|(" ++ name ++ "->_|_)->_|_" ++ gips' ++ "|-" ++ name ++ " [Ax]")
      putStrLn ("[" ++ show (level + 5) ++ "] " ++ name ++ "," ++ name ++ "|(" ++ name ++ "->_|_)->_|_" ++ gips' ++ "|-" ++ name ++ "|(" ++ name ++ "->_|_) [Il|]")
      putStrLn ("[" ++ show (level + 4) ++ "] " ++ name ++ "," ++ name ++ "|(" ++ name ++ "->_|_)->_|_" ++ gips' ++ "|-_|_ [E->]")
      putStrLn ("[" ++ show (level + 3) ++ "] " ++ name ++ "|(" ++ name ++ "->_|_)->_|_" ++ gips' ++ "|-" ++ name ++ "->_|_ [I->]")
      putStrLn ("[" ++ show (level + 2) ++ "] " ++ name ++ "|(" ++ name ++ "->_|_)->_|_" ++ gips' ++ "|-" ++ name ++ "|(" ++ name ++ "->_|_) [Ir|]")
      putStrLn ("[" ++ show (level + 1) ++ "] " ++ name ++ "|(" ++ name ++ "->_|_)->_|_" ++ gips' ++ "|-_|_ [E->]")
      putStrLn ("[" ++ show level ++ "] " ++ gips ++ "|-" ++ name ++ "|(" ++ name ++ "->_|_) [E!!]")
    

    checkCorrect :: Int -> [String] -> [Bool] -> StatExpr -> Maybe String
    checkCorrect 0 names values exp = if evalExpr exp names values then Nothing else Just (getError names values)
    checkCorrect cnt names values exp = do
      let res = checkCorrect (cnt - 1) names (False : values) exp
      if res == Nothing
        then checkCorrect (cnt - 1) names (True : values) exp
        else res

    evalExpr :: StatExpr -> [String] -> [Bool] -> Bool
    evalExpr (SE_Var var) names values = podzalupik var names values
    evalExpr SE_Not _ _ = False
    evalExpr (SE_Or a b) names values = evalExpr a names values || evalExpr b names values
    evalExpr (SE_And a b) names values = evalExpr a names values && evalExpr b names values
    evalExpr (SE_Con a b) names values = not (evalExpr a names values) || evalExpr b names values

    podzalupik :: String -> [String] -> [Bool] -> Bool
    podzalupik x (y : rect1) (val : rect2)
      | x == y = val
      | otherwise = podzalupik x rect1 rect2

    getError :: [String] -> [Bool] -> String
    getError a b = "Formula is refutable [" ++ errorArgs a b ++ "]"

    errorArgs :: [String] -> [Bool] -> String
    errorArgs [] [] = ""
    errorArgs [a] [b] = a ++ ":=" ++ showBool b
    errorArgs (a : rect1) (b : rect2) = a ++ ":=" ++ showBool b ++ "," ++ errorArgs rect1 rect2

    showBool :: Bool -> String
    showBool True = "T"
    showBool False = "F"

    getNames :: StatExpr -> [String]
    getNames (SE_Con a b) = unite (getNames a) (getNames b)
    getNames (SE_And a b) = unite (getNames a) (getNames b)
    getNames (SE_Or a b) = unite (getNames a) (getNames b)
    getNames SE_Not = []
    getNames (SE_Var name) = [name]

    unite :: [String] -> [String] -> [String]
    unite a b = a ++ skipCopy a b

    skipCopy :: [String] -> [String] -> [String]
    skipCopy a (b : rect)
      | inList a b = skipCopy a rect
      | otherwise = b : skipCopy a rect
    skipCopy _ [] = []

    inList :: [String] -> String -> Bool
    inList (a : rect) b
      | a == b = True
      | otherwise = inList rect b
    inList [] _ = False

data StatExpr
  = SE_Var String
  | SE_Not
  | SE_And StatExpr StatExpr
  | SE_Or StatExpr StatExpr
  | SE_Con StatExpr StatExpr
  | SE_Error

delJust :: Maybe a -> a
delJust (Just x) = x

newtype Parser s a = Parser {runParser :: [s] -> Maybe (a, [s])}

instance Functor (Parser s) where
  fmap f (Parser p) = Parser $ \ss -> case p ss of
    Nothing -> Nothing
    Just (x, ss') -> Just (f x, ss')

instance Applicative (Parser s) where
  pure x = Parser $ \ss -> Just (x, ss)

  Parser pf <*> Parser px = Parser $ \ss -> case pf ss of
    Nothing -> Nothing
    Just (f, ss') -> case px ss' of
      Nothing -> Nothing
      Just (x, ss'') -> Just (f x, ss'')

instance Monad (Parser s) where
  Parser p >>= f = Parser $ \ss -> case p ss of
    Nothing -> Nothing
    Just (x, ss') -> runParser (f x) ss'

instance Alternative (Parser s) where
  empty = Parser $ const Nothing

  Parser p1 <|> Parser p2 = Parser $ \ss -> case p1 ss of
    Nothing -> p2 ss
    Just (x, ss') -> Just (x, ss')

eof :: Parser s ()
eof = Parser $ \case
  [] -> Just ((), [])
  _ -> Nothing

satisfies :: (s -> Bool) -> Parser s s
satisfies predicate = Parser $ \case
  [] -> Nothing
  (s : ss') -> if predicate s then Just (s, ss') else Nothing

element :: (Eq s) => s -> Parser s s
element s = satisfies (== s)

instance Show StatExpr where
  show = \case
    SE_Var x -> x
    SE_And l r -> "(" ++ show l ++ "&" ++ show r ++ ")"
    SE_Or l r -> "(" ++ show l ++ "|" ++ show r ++ ")"
    SE_Con l r -> "(" ++ show l ++ "->" ++ show r ++ ")"
    SE_Not -> "_|_"

data StatToken
  = ST_Var String
  | ST_Not
  | ST_And
  | ST_Or
  | ST_Con
  | ST_LPAR
  | ST_RPAR
  deriving (Eq, Show)

instance MonadFail (Parser s) where
  fail _ = Control.Applicative.empty

tokenizeStat :: String -> [StatToken]
tokenizeStat [] = []
tokenizeStat ('_' : ('|' : ('_' : rest))) = ST_Not : tokenizeStat rest
tokenizeStat ('&' : rest) = ST_And : tokenizeStat rest
tokenizeStat ('|' : rest) = ST_Or : tokenizeStat rest
tokenizeStat ('-' : ('>' : rest)) = ST_Con : tokenizeStat rest
tokenizeStat ('(' : rest) = ST_LPAR : tokenizeStat rest
tokenizeStat (')' : rest) = ST_RPAR : tokenizeStat rest
tokenizeStat s@(h : _)
  | isSpace h =
      let (_, rest) = GHC.List.span isSpace s
       in tokenizeStat rest
  | isUpper h =
      let (letters, rest) = GHC.List.span (\c -> isUpper c || isNumber c || ord c == 39) s
       in ST_Var letters : tokenizeStat rest
tokenizeStat _ = []

parseExpr :: Parser StatToken StatExpr
parseExpr =
  ( do
      x <- parseDis
      element ST_Con
      SE_Con x <$> parseExpr
  )
    <|> parseDis

parseDis :: Parser StatToken StatExpr
parseDis = parseCon >>= parseDis'

parseDis' :: StatExpr -> Parser StatToken StatExpr
parseDis' acc =
  ( do
      element ST_Or
      x <- parseCon
      parseDis' (SE_Or acc x)
  )
    <|> pure acc

parseCon :: Parser StatToken StatExpr
parseCon = parseNot >>= parseCon'

parseCon' :: StatExpr -> Parser StatToken StatExpr
parseCon' acc =
  ( do
      element ST_And
      x <- parseNot
      parseCon' (SE_And acc x)
  )
    <|> pure acc

parseNot :: Parser StatToken StatExpr
parseNot =
  ( do
      element ST_Not
      pure SE_Not
  )
    <|> ( do
            element ST_LPAR
            x <- parseExpr
            element ST_RPAR
            pure x
        )
    <|> ( do
            ST_Var x <- satisfies (\case ST_Var _ -> True; _ -> False)
            pure (SE_Var x)
        )

parseks :: String -> Maybe StatExpr
parseks s = fst <$> runParser (parseExpr <* eof) (tokenizeStat s)