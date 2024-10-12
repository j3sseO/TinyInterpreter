{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module TINYParser where

import Parsing

type Ide = String

data Exp
    = Zero
    | One
    | TT
    | FF
    | Read
    | I Ide
    | Not Exp
    | Equal Exp Exp
    | Plus Exp Exp
    deriving Show

expr :: Parser Exp
expr = do
    e1 <- term
    symbol "+"
    e2 <- expr
    return (Plus e1 e2)
  +++ do
    e1 <- term
    symbol "="
    e2 <- expr
    return (Equal e1 e2)
  +++ term

term :: Parser Exp
term = do
    symbol "not"
    e <- expr
    return (Not e)
  +++ factor

factor :: Parser Exp
factor = do
    symbol "read"
    return Read
  +++ do
    symbol "false"
    return FF
  +++ do
    symbol "true"
    return TT
  +++ do
    symbol "0"
    return Zero
  +++ do
    symbol "1"
    return One
  +++ do
    i <- token identifier
    return (I i)
  +++ do
    symbol "("
    e <- expr
    symbol ")"
    return e

data Cmd
    = Assign Ide Exp
    | Output Exp
    | Seq Cmd Cmd
    | IfThenElse Exp Cmd Cmd
    | WhileDo Exp Cmd
    deriving Show

cmd :: Parser Cmd
cmd = do
    i <- token identifier
    symbol ":="
    e <- expr
    return (Assign i e)
  +++ do
    symbol "output"
    e <- expr
    return (Output e)
  +++ do
    symbol "if"
    e <- expr
    symbol "then"
    c1 <- cmd
    symbol "else"
    c2 <- cmd
    return (IfThenElse e c1 c2)
  +++ do
    symbol "while"
    e <- expr
    symbol "do"
    c <- cmd
    return (WhileDo e c)
  +++ do
    symbol "("
    c <- cmd
    symbol ")"
    return c

cparse :: String -> Cmd
cparse xs =
    case parse cmd xs of
        [(n, [])] -> n
        [(_, out)] -> error ("unused input " ++ out)
        [] -> error "invalid input"

gordon = "sum := 0; x := read; (while not (x = true) do (sum := sum + x; x := read)); output sum"
first = "output read + read; output 0"
second = gordon
third = "sum := 0; n := read; j := 0; (while not (j = n) do sum := sum + j + 1; j := j + 1); output sum"
fourth = "prod := 0; m := read; p := read; i := 0; (while not (i = m) do prod := prod + p; i := i + 1); output prod"
fifth = "fact := 1; n := read; j := 0; (while not (j = n) do prod := 0; m := fact; p := j + 1; i := 0; (while not (i = m) do prod := prod + p; i := i + 1); fact := prod; j := j + 1); output fact"
