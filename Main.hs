{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use camelCase" #-}

module Main (main) where

import Control.Applicative
import Data.Char
import GHC.List

main :: IO ()
main = do
  z <- getLine
  putStrLn (show (delJust (parseStatExpr z)))

delJust :: (Maybe StatExpr) -> StatExpr
delJust (Just x) = x


safeDiv :: Int -> Int -> Maybe Int
safeDiv x y = if y == 0 then Nothing else Just (div x y)

safeDiv' :: Int -> Int -> Either String Int
safeDiv' x y = if y == 0 then Left "ops error" else Right (div x y)

newtype T m a = MkT (m a)

class ToString a where
  toString :: a -> String

instance ToString Bool where
  toString True = "heh"
  toString False = "hah"

instance ToString Int where
  toString = show

class Equ a where
  (===) :: a -> a -> Bool
  x === y = not (x /== y)
  (/==) :: a -> a -> Bool
  x /== y = not (x === y)

  {-# MINIMAL (===) | (/==) #-}

instance Equ () where
  () === () = True

newtype Plus = MkPlus Int

newtype Times = MkTimes Int

instance Semigroup Plus where
  MkPlus x <> MkPlus y = MkPlus (x + y)

instance Monoid Plus where
  mempty = MkPlus 0

instance Semigroup Times where
  MkTimes x <> MkTimes y = MkTimes (x + y)

instance Monoid Times where
  mempty = MkTimes 1

newtype Parser s a = Parser {runParser :: [s] -> Maybe (a, [s])}

data Option a = None | Some a

instance Functor Option where
  fmap f None = None
  fmap f (Some x) = Some (f x)

instance Functor (Parser s) where
  fmap f (Parser p) = Parser $ \ss -> case p ss of
    Nothing -> Nothing
    Just (x, ss') -> Just (f x, ss')

instance Applicative Option where
  pure = Some
  None <*> _ = None
  Some _ <*> None = None
  Some f <*> Some x = Some $ f x

instance Applicative (Parser s) where
  pure x = Parser $ \ss -> Just (x, ss)

  Parser pf <*> Parser px = Parser $ \ss -> case pf ss of
    Nothing -> Nothing
    Just (f, ss') -> case px ss' of
      Nothing -> Nothing
      Just (x, ss'') -> Just (f x, ss'')

instance Monad Option where
  None >>= _ = None
  Some x >>= f = f x

instance Monad (Parser s) where
  Parser p >>= f = Parser $ \ss -> case p ss of
    Nothing -> Nothing
    Just (x, ss') -> runParser (f x) ss'

instance MonadFail (Parser s) where
  fail _ = empty

instance Alternative Option where
  empty = None

  None <|> o2 = o2
  Some x <|> _ = Some x

instance Alternative (Parser s) where
  empty = Parser $ \_ -> Nothing

  Parser p1 <|> Parser p2 = Parser $ \ss -> case p1 ss of
    Nothing -> p2 ss
    Just (x, ss') -> Just (x, ss')

ok :: Parser s ()
ok = pure ()

eof :: Parser s ()
eof = Parser $ \case
  [] -> Just ((), [])
  _ -> Nothing

pHead :: Parser s s
pHead = Parser $ \case
  [] -> Nothing
  (s : ss') -> Just (s, ss')

satisfies :: (s -> Bool) -> Parser s s
satisfies predicate = Parser $ \case
  [] -> Nothing
  (s : ss') -> if predicate s then Just (s, ss') else Nothing

element :: (Eq s) => s -> Parser s s
element s = satisfies (== s)

stream :: (Eq s) => [s] -> Parser s [s]
stream [] = pure []
stream (s : ss') = element s >>= \ps -> stream ss' >>= \pss' -> pure (ps : pss')

infixl 6 :+, :-

infixl 7 :*

infixl 8 :^

data ArithExpr
  = AE_Int Int
  | ArithExpr :+ ArithExpr
  | ArithExpr :- ArithExpr
  | ArithExpr :* ArithExpr
  | ArithExpr :^ ArithExpr
  | AE_Neg ArithExpr

instance Show ArithExpr where
  show = \case
    AE_Int x -> show x
    l :+ r -> "(" ++ show l ++ " + " ++ show r ++ ")"
    l :- r -> "(" ++ show l ++ " - " ++ show r ++ ")"
    l :* r -> "(" ++ show l ++ " * " ++ show r ++ ")"
    l :^ r -> "(" ++ show l ++ " ^ " ++ show r ++ ")"
    AE_Neg x -> "(-" ++ show x ++ ")"

data AEException = AE_NegtiveExponent | AE_ZeroToTheZerothPower deriving (Eq, Show)

eval :: ArithExpr -> Either AEException Int
eval (AE_Int x) = pure x
eval (l :+ r) = liftA2 (+) (eval l) (eval r)
eval (l :- r) = liftA2 (-) (eval l) (eval r)
eval (l :* r) = liftA2 (*) (eval l) (eval r)
eval (l :^ r) =
  eval l >>= \a ->
    eval r >>= \b ->
      if a == 0 && b == 0
        then Left AE_ZeroToTheZerothPower
        else
          if b < 0
            then Left AE_NegtiveExponent
            else pure (a + b)
eval (AE_Neg x) = negate <$> eval x

data ArithToken
  = AT_Digits Int
  | AT_Plus
  | AT_Minus
  | AT_Times
  | AT_Power
  | AT_LPAR
  | AT_RPAR
  | AT_HALT
  deriving (Eq, Show)

tokenize :: String -> [ArithToken]
tokenize [] = []
tokenize ('+' : rest) = AT_Plus : tokenize rest
tokenize ('-' : rest) = AT_Minus : tokenize rest
tokenize ('*' : rest) = AT_Times : tokenize rest
tokenize ('^' : rest) = AT_Power : tokenize rest
tokenize ('(' : rest) = AT_LPAR : tokenize rest
tokenize (')' : rest) = AT_RPAR : tokenize rest
tokenize s@(h : _)
  | isSpace h =
      let (spaces, rest) = GHC.List.span isSpace s
       in tokenize rest
  | isDigit h =
      let (digits, rest) = GHC.List.span isDigit s
       in AT_Digits (read digits) : tokenize rest
tokenize _ = [AT_HALT]

parseE :: Parser ArithToken ArithExpr
parseE = parseT >>= \t -> parseE' t

parseE' :: ArithExpr -> Parser ArithToken ArithExpr
parseE' acc =
  ( do
      element AT_Plus
      t <- parseT
      parseE' (acc :+ t)
  )
    <|> ( do
            element AT_Minus
            t <- parseT
            parseE' (acc :- t)
        )
    <|> pure acc

parseT :: Parser ArithToken ArithExpr
parseT = parseF >>= parseT'

parseT' :: ArithExpr -> Parser ArithToken ArithExpr
parseT' acc =
  ( do
      element AT_Times
      f <- parseF
      parseT' (acc :* f)
  )
    <|> pure acc

parseF :: Parser ArithToken ArithExpr
parseF =
  ( do
      x <- parseX
      element AT_Power
      f <- parseF
      pure (x :^ f)
  )
    <|> parseX

parseX :: Parser ArithToken ArithExpr
parseX =
  ( do
      element AT_Minus
      AE_Neg <$> parseX
  )
    <|> ( do
            element AT_LPAR
            e <- parseE
            element AT_RPAR
            pure e
        )
    <|> ( do
            AT_Digits i <- satisfies (\case AT_Digits i -> True; _ -> False)
            pure (AE_Int i)
        )

parseArithExpr :: String -> Maybe ArithExpr
parseArithExpr s = fst <$> runParser (parseE <* eof) (tokenize s)

data StatExpr
  = SE_Var String
  | SE_Not StatExpr
  | SE_And StatExpr StatExpr
  | SE_Or StatExpr StatExpr
  | SE_Con StatExpr StatExpr

instance Show StatExpr where
  show = \case
    SE_Var x -> x
    SE_And l r -> "(&," ++ show l ++ "," ++ show r ++ ")"
    SE_Or l r -> "(|," ++ show l ++ "," ++ show r ++ ")"
    SE_Con l r -> "(->," ++ show l ++ "," ++ show r ++ ")"
    SE_Not x -> "(!" ++ show x ++ ")"

data StatToken
  = ST_Var String
  | ST_Not
  | ST_And
  | ST_Or
  | ST_Con
  | ST_LPAR
  | ST_RPAR
  deriving (Eq, Show)

tokenizeStat :: String -> [StatToken]
tokenizeStat [] = []
tokenizeStat ('!' : rest) = ST_Not : tokenizeStat rest
tokenizeStat ('&' : rest) = ST_And : tokenizeStat rest
tokenizeStat ('|' : rest) = ST_Or : tokenizeStat rest
tokenizeStat ('-' : ('>' : rest)) = ST_Con : tokenizeStat rest
tokenizeStat ('(' : rest) = ST_LPAR : tokenizeStat rest
tokenizeStat (')' : rest) = ST_RPAR : tokenizeStat rest
tokenizeStat s@(h : _)
  | isSpace h =
      let (spaces, rest) = GHC.List.span isSpace s
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
      f <- parseExpr
      pure (SE_Con x f)
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
      SE_Not <$> parseNot
  )
    <|> ( do
            element ST_LPAR
            x <- parseExpr
            element ST_RPAR
            pure x
        )
    <|> ( do
            ST_Var x <- satisfies (\case ST_Var i -> True; _ -> False)
            pure (SE_Var x)
        )

parseStatExpr s = fst <$> runParser (parseExpr <* eof) (tokenizeStat s)

{-

parseT :: Parser ArithToken ArithExpr
parseT = parseF >>= parseT'

parseT' :: ArithExpr -> Parser ArithToken ArithExpr
parseT' acc =
  ( do
      element AT_Times
      f <- parseF
      parseT' (acc :* f)
  )
    <|> pure acc

parseX :: Parser ArithToken ArithExpr
parseX =
  ( do
      element AT_Minus
      AE_Neg <$> parseX
  )
    <|> ( do
            element AT_LPAR
            e <- parseE
            element AT_RPAR
            pure e
        )
    <|> ( do
            AT_Digits i <- satisfies (\case AT_Digits i -> True; _ -> False)
            pure (AE_Int i)
        )

        -}
