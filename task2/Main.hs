{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-compat-unqualified-imports #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Control.Applicative
  ( Alternative (empty, (<|>)),
  )
import Data.Array.IO
  ( IOArray,
    MArray (newArray),
    getAssocs,
    readArray,
    writeArray,
  )
import Data.Array.IO.Internals (IOArray (IOArray))
import Data.Char (isNumber, isSpace, isUpper, ord)
import Data.List (sortBy)
import Data.Sequence
  ( Seq,
    ViewL ((:<)),
    empty,
    fromList,
    null,
    singleton,
    viewl,
    (<|),
    (><),
  )
import GHC.List (span)
import Prelude hiding (exp, last, mod)

data Proof
  = Hyp StatExpr
  | Ax StatExpr
  | MP StatExpr StatExpr
  | Ded StatExpr StatExpr
  | Inc
  deriving (Show, Eq)

data Key
  = MP_Key Int (Int, Int)
  | Ded_Key Int Int
  | Ax_Key Int
  | Hyp_Key Int
  | Inc_Key Int
  deriving (Show)

delJust :: Maybe a -> a
delJust (Just x) = x

main :: IO ()
main =
  do
    content <- getContents
    (proofs, keys, mx) <- loop [] 1 (lines content)
    return ()

-- fl <- newArray (1, mx) Data.Sequence.empty :: IO (IOArray Int (Seq Proof))
-- need <- newArray (1, mx) False :: IO (IOArray Int Bool)

-- result <- solve proofs keys fl need mx
-- printResult (Data.Sequence.viewl result)

getLines :: IO [String]
getLines = do
  x <- getLine
  if x == ""
    then return []
    else do
      xs <- getLines
      return (x : xs)

------------------------------------------------------------------------------

loop :: [(StatExpr, [StatExpr])] -> Int -> [String] -> IO ([Proof], [Key], Int)
loop last i (line : linesss) =
  do
    let tokens = tokenizeStat line
        gips = getGips tokens []
        sorted_gips = Data.List.sortBy (\a b -> compare (show a) (show b)) gips
        exp = getExp tokens
        ax = isAx 1 exp
        gip = isGip gips 1 exp
    let mod = isModFast 1 last exp sorted_gips
        ded = isDed 1 last (Data.List.sortBy (\a b -> compare (show a) (show b)) (bolsheGips exp ++ gips)) (lastik exp)
        proof
          | ax /= -1 = Ax exp
          | gip /= -1 = Hyp exp
          | mod /= Nothing = MP exp (snd (delJust mod))
          | ded /= Nothing = Ded exp (snd (delJust ded))
          | otherwise = Inc
        key
          | ax /= -1 = Ax_Key i
          | gip /= -1 = Hyp_Key i
          | mod /= Nothing = MP_Key i (fst (delJust mod))
          | ded /= Nothing = Ded_Key i (fst (delJust ded))
          | otherwise = Inc_Key i
        result
          | ax /= -1 = "[" ++ show i ++ "] " ++ line ++ " [Ax. sch. " ++ show ax ++ "]"
          | gip /= -1 = "[" ++ show i ++ "] " ++ line ++ " [Hyp. " ++ show gip ++ "]"
          | mod /= Nothing = "[" ++ show i ++ "] " ++ line ++ " [M.P. " ++ show (fst (fst (delJust mod))) ++ ", " ++ show (snd (fst (delJust mod))) ++ "]"
          | ded /= Nothing = "[" ++ show i ++ "] " ++ line ++ " [Ded. " ++ show (fst (delJust ded)) ++ "]"
          | otherwise = "[" ++ show i ++ "] " ++ line ++ " [Incorrect]"
    putStrLn result
    (proofs, keys, mxx) <- loop (last ++ [(exp, sorted_gips)]) (i + 1) linesss
    -- when (proofs == []) (putStrLn line)
    let mx = if proofs == [] then i else mxx
    return (proofs ++ [proof], keys ++ [key], mx)
loop _ _ _ = return ([], [], 0)

when :: (Applicative f) => Bool -> f () -> f ()
when p act = if p then act else pure ()

-----------------------------------------------------------------------------------------

solve :: [Proof] -> [Key] -> IOArray Int (Seq Proof) -> IOArray Int Bool -> Int -> IO (Seq Proof)
solve solve_p solve_k fl need mx = do
  writeArray need mx True
  calcNode solve_p solve_k

  readArray fl mx
  where
    calcNode :: [Proof] -> [Key] -> IO ()
    calcNode (Ax exp : rect1) (Ax_Key key : rect2) = do
      flag <- readArray need key
      if not flag
        then calcNode rect1 rect2
        else do
          calcNode rect1 rect2
          let res = Data.Sequence.singleton (Ax exp)
          writeArray fl key res
    calcNode (Hyp exp : rect1) (Hyp_Key key : rect2) = do
      flag <- readArray need key
      if not flag
        then calcNode rect1 rect2
        else do
          calcNode rect1 rect2
          let res = Data.Sequence.singleton (Hyp exp)

          writeArray fl key res
    calcNode (MP exp how : rect1) (MP_Key key (l, r) : rect2) = do
      flag <- readArray need key
      if not flag
        then calcNode rect1 rect2
        else do
          writeArray need l True
          writeArray need r True
          calcNode rect1 rect2
          left <- readArray fl l
          right <- readArray fl r
          let res = Data.Sequence.singleton (MP exp how) >< left >< right
          writeArray need key True
          writeArray fl key res
    calcNode (Ded exp pred_exp : rect1) (Ded_Key key x : rect2) = do
      flag <- readArray need key
      if not flag
        then calcNode rect1 rect2
        else do
          writeArray need x True
          calcNode rect1 rect2
          proof <- readArray fl x
          let l = depth exp
              r = depth pred_exp
              k = calcEq l r exp pred_exp
              x_proof = calcPredExp pred_exp (r - k)
              res = refactorProof (x_proof >< proof) exp (l - k)
          writeArray fl key res
    calcNode [] [] = return ()

calcEq :: Int -> Int -> StatExpr -> StatExpr -> Int
calcEq l r (SE_Con _ b) x
  | l > r = calcEq (l - 1) r b x
calcEq l r x (SE_Con _ d)
  | l < r = calcEq l (r - 1) x d
calcEq l r (SE_Con a b) (SE_Con c d)
  | l == r = if SE_Con a b == SE_Con c d then l else calcEq (l - 1) (r - 1) b d
calcEq 1 1 _ _ = 1

depth :: StatExpr -> Int
depth (SE_Con _ b) = depth b + 1
depth _ = 1

printResult :: ViewL Proof -> IO ()
printResult (proof :< rect) = do
  printResult (Data.Sequence.viewl rect)
  putStrLn (show (getExpProof proof))
printResult _ = do
  return ()

refactorProof :: Seq Proof -> StatExpr -> Int -> Seq Proof
refactorProof proof _ 0 = proof
refactorProof proof (SE_Con a b) k = addHyp (refactorProof proof b (k - 1)) a

addHyp :: Seq Proof -> StatExpr -> Seq Proof
addHyp proofs a
  | Data.Sequence.null proofs = Data.Sequence.empty
  | otherwise = do
      let (proof :< rect) = Data.Sequence.viewl proofs
      addA proof a >< addHyp rect a

addA :: Proof -> StatExpr -> Seq Proof
addA (MP exp l) a =
  Data.Sequence.fromList
    [ MP (SE_Con a exp) (SE_Con a (SE_Con l exp)),
      MP (SE_Con (SE_Con a (SE_Con l exp)) (SE_Con a exp)) (SE_Con a l),
      Ax (SE_Con (SE_Con a l) (SE_Con (SE_Con a (SE_Con l exp)) (SE_Con a exp)))
    ]
addA (Ax exp) a =
  Data.Sequence.fromList
    [ MP (SE_Con a exp) exp,
      Ax exp,
      Ax (SE_Con exp (SE_Con a exp))
    ]
addA x a
  | getExpProof x == a =
      Data.Sequence.fromList
        [ MP (SE_Con a a) (SE_Con a (SE_Con (SE_Con a a) a)),
          Ax (SE_Con a (SE_Con (SE_Con a a) a)),
          MP (SE_Con (SE_Con a (SE_Con (SE_Con a a) a)) (SE_Con a a)) (SE_Con a (SE_Con a a)),
          Ax (SE_Con (SE_Con a (SE_Con a a)) (SE_Con (SE_Con a (SE_Con (SE_Con a a) a)) (SE_Con a a))),
          Ax (SE_Con a (SE_Con a a))
        ]
addA (Hyp exp) a =
  Data.Sequence.fromList
    [ MP (SE_Con a exp) exp,
      Hyp exp,
      Ax (SE_Con exp (SE_Con a exp))
    ]
addA _ _ = Data.Sequence.empty

getExpProof :: Proof -> StatExpr
getExpProof (Ax exp) = exp
getExpProof (Hyp exp) = exp
getExpProof (MP exp _) = exp
getExpProof (Ded exp _) = exp
getExpProof Inc = SE_Var "A"

calcPredExp :: StatExpr -> Int -> Seq Proof
calcPredExp _ 0 = Data.Sequence.empty
calcPredExp (SE_Con a b) k = calcPredExp b (k - 1) >< Data.Sequence.fromList [MP b a, Hyp a]

----------------------------------------------------------------------------------------

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

instance MonadFail (Parser s) where
  fail _ = Control.Applicative.empty

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

data StatExpr
  = SE_Var String
  | SE_Not StatExpr
  | SE_And StatExpr StatExpr
  | SE_Or StatExpr StatExpr
  | SE_Con StatExpr StatExpr
  deriving (Eq)

data StatToken
  = ST_Var String
  | ST_Not
  | ST_And
  | ST_Or
  | ST_Con
  | ST_LPAR
  | ST_RPAR
  | ST_Next
  | ST_Exp
  deriving (Eq, Show)

tokenizeStat :: String -> [StatToken]
tokenizeStat [] = []
tokenizeStat ('|' : ('-' : rest)) = ST_Exp : tokenizeStat rest
tokenizeStat ('-' : ('>' : rest)) = ST_Con : tokenizeStat rest
tokenizeStat ('|' : rest) = ST_Or : tokenizeStat rest
tokenizeStat ('!' : rest) = ST_Not : tokenizeStat rest
tokenizeStat ('&' : rest) = ST_And : tokenizeStat rest
tokenizeStat ('(' : rest) = ST_LPAR : tokenizeStat rest
tokenizeStat (')' : rest) = ST_RPAR : tokenizeStat rest
tokenizeStat (',' : rest) = ST_Next : tokenizeStat rest
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
      SE_Not <$> parseNot
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

instance Show StatExpr where
  show = \case
    SE_Var x -> x
    SE_And l r -> "(" ++ show l ++ "&" ++ show r ++ ")"
    SE_Or l r -> "(" ++ show l ++ "|" ++ show r ++ ")"
    SE_Con l r -> "(" ++ show l ++ "->" ++ show r ++ ")"
    SE_Not x -> "(" ++ "!" ++ show x ++ ")"

-----------------------------------------------------------------------------------------

getGips :: [StatToken] -> [StatToken] -> [StatExpr]
getGips (ST_Exp : _) rest1 = [delJust (fst <$> runParser (parseExpr <* eof) rest1) | rest1 /= []]
getGips (ST_Next : (x : rest)) rest1 = delJust (fst <$> runParser (parseExpr <* eof) rest1) : getGips rest [x]
getGips (x : rest) rest1 = getGips rest (rest1 ++ [x])

getExp :: [StatToken] -> StatExpr
getExp (ST_Exp : rest) = delJust (fst <$> runParser (parseExpr <* eof) rest)
getExp (_ : rest) = getExp rest

isGip :: [StatExpr] -> Int -> StatExpr -> Int
isGip (x : rest) y z = if x == z then y else isGip rest (y + 1) z
isGip [] _ _ = -1

isAx :: Int -> StatExpr -> Int
isAx 11 _ = -1
isAx x y = if eqAx x y then x else isAx (x + 1) y

eqAx :: Int -> StatExpr -> Bool
eqAx 1 (SE_Con a (SE_Con _ aa)) = a == aa
eqAx 2 (SE_Con (SE_Con a b) (SE_Con (SE_Con aa (SE_Con bb c)) (SE_Con aaa cc))) = a == aa && aa == aaa && b == bb && c == cc
eqAx 3 (SE_Con a (SE_Con b (SE_And aa bb))) = a == aa && b == bb
eqAx 4 (SE_Con (SE_And a _) aa) = a == aa
eqAx 5 (SE_Con (SE_And _ b) bb) = b == bb
eqAx 6 (SE_Con a (SE_Or aa _)) = a == aa
eqAx 7 (SE_Con b (SE_Or _ bb)) = b == bb
eqAx 8 (SE_Con (SE_Con a c) (SE_Con (SE_Con b cc) (SE_Con (SE_Or aa bb) ccc))) = a == aa && c == cc && cc == ccc && b == bb
eqAx 9 (SE_Con (SE_Con a b) (SE_Con (SE_Con aa (SE_Not bb)) (SE_Not aaa))) = a == aa && aa == aaa && b == bb
eqAx 10 (SE_Con (SE_Not (SE_Not a)) aa) = a == aa
eqAx _ _ = False

isModFast :: Int -> [(StatExpr, [StatExpr])] -> StatExpr -> [StatExpr] -> Maybe ((Int, Int), StatExpr)
isModFast _ [] _ _ = Nothing
isModFast x ((e, g) : rect) exp gip = if g == gip then (let y = isModEbash (x + 1) rect e exp gip in if fst y == 0 then isModFast (x + 1) rect exp gip else (if fst y < 0 then Just ((x, -(fst y)), e) else Just ((fst y, x), snd y))) else isModFast (x + 1) rect exp gip

isModEbash :: Int -> [(StatExpr, [StatExpr])] -> StatExpr -> StatExpr -> [StatExpr] -> (Int, StatExpr)
isModEbash _ [] _ _ _ = (0, SE_Var "A")
isModEbash x ((e, g) : rect) el exp gip = if gip == g then (if uraaMod e el exp then (x, e) else (if uraaMod el e exp then (-x, e) else isModEbash (x + 1) rect el exp gip)) else isModEbash (x + 1) rect el exp gip

uraaMod :: StatExpr -> StatExpr -> StatExpr -> Bool
uraaMod a (SE_Con aa bb) b = a == aa && b == bb
uraaMod _ _ _ = False

isDed :: Int -> [(StatExpr, [StatExpr])] -> [StatExpr] -> StatExpr -> Maybe (Int, StatExpr)
isDed _ [] _ _ = Nothing
isDed x ((e, g) : rect) eg lexp =
  if eg
    == Data.List.sortBy (\a b -> compare (show a) (show b)) (bolsheGips e ++ g)
    && (lastik e == lexp)
    then Just (x, e)
    else isDed (x + 1) rect eg lexp

bolsheGips :: StatExpr -> [StatExpr]
bolsheGips (SE_Con x y) = x : bolsheGips y
bolsheGips _ = []

lastik :: StatExpr -> StatExpr
lastik (SE_Con _ y) = lastik y
lastik x = x