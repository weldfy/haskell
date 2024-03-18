{-# OPTIONS_GHC -Wno-compat-unqualified-imports #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
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
    readArray,
    writeArray,
  )
import Data.Char (isLower, isNumber, isSpace, isUpper)
import GHC.List (span)
import Parser
import Tokenizer
import Prelude hiding (exp, last, mod)

delJust :: Maybe a -> a
delJust (Just x) = x

main :: IO ()
main =
  do
    theta <- newArray (1, 1) SE_Null :: IO (IOArray Int StatExpr)
    s <- getLine
    -- putStrLn $ show $ parse $ alexScanTokens s

    result <- solve theta (parse $ alexScanTokens s)
    putStrLn result

solve :: IOArray Int StatExpr -> StatExpr -> IO String
solve theta exp = do
  (res11, phi11, x11) <- check11 exp
  theta11 <- readArray theta 1

  writeArray theta 1 SE_Null
  (res12, phi12, x12) <- check12 exp
  theta12 <- readArray theta 1
  return
    ( if res11 == 2
        then "Axiom scheme 11, phi = " ++ show phi11 ++ ", x = " ++ x11 ++ ", theta = " ++ if show theta11 == "ZALUPA" then x11 else show theta11
        else
          if res12 == 2
            then "Axiom scheme 12, phi = " ++ show phi12 ++ ", x = " ++ x12 ++ ", theta = " ++ if show theta12 == "ZALUPA" then x12 else show theta12
            else
              if res11 == 1
                then "Similar to axiom scheme 11, phi = " ++ show phi11 ++ ", x = " ++ x11 ++ ", theta = " ++ if show theta11 == "ZALUPA" then x11 else show theta11
                else
                  if res12 == 1
                    then "Similar to axiom scheme 12, phi = " ++ show phi12 ++ ", x = " ++ x12 ++ ", theta = " ++ if show theta12 == "ZALUPA" then x12 else show theta12
                    else "Not an axiom scheme 11 or 12"
    )
  where
    check11 :: StatExpr -> IO (Int, StatExpr, String)
    check11 (SE_Con (SE_All x phi) exp) = do
      res <- getTheta x [] phi exp
      return (res, phi, x)
    check11 _ = do
      return (0, SE_LastArg, "")

    check12 :: StatExpr -> IO (Int, StatExpr, String)
    check12 (SE_Con exp (SE_One x phi)) = do
      res <- getTheta x [] phi exp
      return (res, phi, x)
    check12 _ = do
      return (0, SE_LastArg, "")

    getTheta :: String -> [String] -> StatExpr -> StatExpr -> IO Int
    getTheta x y (SE_Con a b) (SE_Con c d) = do
      l <- getTheta x y a c
      r <- getTheta x y b d
      return (min l r)
    getTheta x y (SE_And a b) (SE_And c d) = do
      l <- getTheta x y a c
      r <- getTheta x y b d
      return (min l r)
    getTheta x y (SE_Or a b) (SE_Or c d) = do
      l <- getTheta x y a c
      r <- getTheta x y b d
      return (min l r)
    getTheta x y (SE_Args a b) (SE_Args c d) = do
      l <- getTheta x y a c
      r <- getTheta x y b d
      return (min l r)
    getTheta x y (SE_Not a) (SE_Not b) = do
      getTheta x y a b
    getTheta x y (SE_One c1 a) (SE_One c2 b)
      | c1 == c2 = do
          getTheta x (c1 : y) a b
    getTheta x y (SE_All c1 a) (SE_All c2 b)
      | c1 == c2 = do
          getTheta x (c1 : y) a b
    getTheta x y (SE_Pred c1 a) (SE_Pred c2 b)
      | c1 == c2 = do
          getTheta x y a b
    getTheta x y (SE_Func c1 a) (SE_Func c2 b)
      | c1 == c2 = do
          getTheta x y a b
    getTheta _ _ SE_LastArg SE_LastArg = do
      return 2
    getTheta x arr (SE_Var y) exp
      | x == y = do
          if not (isTerm exp)
            then return 0
            else
              if not (notInList x arr)
                then
                  if SE_Var y == exp
                    then return 2
                    else return 0
                else do
                  t <- readArray theta 1
                  if t == SE_Null
                    then do
                      writeArray theta 1 exp
                      if checkFree exp arr
                        then return 2
                        else return 1
                    else
                      if t == exp
                        then
                          if checkFree t arr
                            then return 2
                            else return 1
                        else return 0
    getTheta _ _ (SE_Var y) (SE_Var z)
      | y == z = do
          return 2
    getTheta _ _ _ _ = do
      return 0

    isTerm :: StatExpr -> Bool
    isTerm (SE_Var _) = True
    isTerm (SE_Func _ _) = True
    isTerm _ = False

    checkFree :: StatExpr -> [String] -> Bool
    checkFree (SE_Func _ exp) b = checkFree exp b
    checkFree (SE_Var x) b = notInList x b
    checkFree (SE_Args x1 x2) b = checkFree x1 b && checkFree x2 b
    checkFree SE_LastArg _ = True

    notInList :: String -> [String] -> Bool
    notInList _ [] = True
    notInList x (y : rect)
      | x == y = False
      | otherwise = notInList x rect

------------------------------------------------------------------------------
