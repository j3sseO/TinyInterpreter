-- The version with display added so we can do error diagnostics
-- NOTE WE CAN DO THIS ONLY FOR VARIABLES x, y and z

-- This is closely based on Robert D. Cameron's code
--  www.cs.sfu.ca/~cameron

-- 1.  Syntactic and Semantic Domains of TINY
--      Syntactic Domains are Ide, Exp and Cmd

-- Note that we are about to import the parser for TINY as a module. For this to work
-- you need to have the parser in a file called TINYParser.lhs in the same directory
-- as this file. Then run ghci with just the filename of this file as the file to load.
-- So, type "ghci CW4_simple_error_TINY_denot.hs" to get the parser to load and then this file.
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant lambda" #-}

import TINYParser

-- We had these definitions in TINYParser....
-- type Ide = String

-- data Exp = Zero | One | TT | FF |
--            Read | I Ide | Not Exp |
--            Equal Exp Exp | Plus Exp Exp
--            deriving Show

-- data Cmd = Assign Ide Exp | Output Exp |
--            IfThenElse Exp Cmd Cmd |
--            WhileDo Exp Cmd |
--            Seq Cmd Cmd
--            deriving Show

-- Semantic Domains

data Value = Numeric Integer | Boolean Bool | ERROR
             deriving Show

data MemVal = Stored Value | Unbound
              deriving Show

-- Here we use functional objects to represent memory.  Looking up
-- an identifier is thus function application.   But we will later
-- need to define functions to initialize and update memory objects,
-- as well.

type Memory = ([Ide], Ide -> MemVal)

type Input = [Value]

type Output = [Value]

type State = (Memory, Input, Output)


-- 2.  Signatures of semantic functions.

-- First, we need auxiliary types to represent the possible
-- results of expression evaluation or command execution.


data ExpVal = OK Value State | Error

data CmdVal = OKc State | Errorc

exp_semantics :: Exp -> State -> ExpVal

cmd_semantics :: Cmd -> State -> CmdVal

-- Note: we can use this interpreter to show errors only in program
--        with variables x, y and z---no others!

display :: Memory -> String
display (m, j) = concat[x ++ "=" ++ show (j x) ++ " " | x <- m]


-- 3. Semantic Equations defining the semantic functions
--     Haskell's equational definition is similar but not
--     identical to the equational style used in the mathematical semantics.

exp_semantics Zero s = OK (Numeric 0) s

exp_semantics One s = OK (Numeric 1) s

exp_semantics TT s = OK (Boolean True) s

exp_semantics FF s = OK (Boolean False) s

exp_semantics Read ((m, j), [], o) = error (display (m, j) ++ "Input: " ++ "[] " ++ "Output: " ++ show o)

exp_semantics Read ((m, j), (i:is), o) = OK i ((m, j), is, o)

exp_semantics (I ident) ((m, j), i, o) =
 case (j ident) of
    Stored v  -> OK v ((m, j), i, o)
    Unbound   -> error (display (m, j) ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)

-- Semantics of the 'Not' expression
exp_semantics (Not exp) s =
    case (exp_semantics exp s) of
    -- If the expression is a boolean, then we negate it
    OK (Boolean v) s1 -> OK (Boolean (not v)) s1
    -- If the expression is a numeric value, we return an error
    OK (Numeric v) s1 -> Error
    -- Else, we return an error
    Error -> error (display (m, j) ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)
                where ((m, j),i,o) = s

exp_semantics (Equal exp1 exp2) s =
 case (exp_semantics exp1 s) of
   OK (Numeric v1) s1 -> case (exp_semantics exp2 s1) of 
                           OK (Numeric v2) s2 -> OK (Boolean (v1 == v2)) s2
                           OK (Boolean v2) s2 -> OK (Boolean False) s2
                           Error -> error (display (m, j) ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)
                                    where ((m, j),i,o) = s1
   OK (Boolean v1) s1 -> case (exp_semantics exp2 s1) of 
                           OK (Boolean v2) s2 -> OK (Boolean (v1 == v2)) s2
                           OK (Numeric v2) s2 -> OK (Boolean False) s2
                           Error -> error (display (m, j) ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)
                                    where ((m, j),i,o) = s1
   Error -> error (display (m, j) ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)
            where ((m, j),i,o) = s

-- Semantics of the 'Plus' expression
exp_semantics (Plus exp1 exp2) s = 
    case (exp_semantics exp1 s) of
    -- If the first expression is a numeric value, we continue to evaluate the second expression
    OK (Numeric v1) s1 -> case (exp_semantics exp2 s1) of 
                            -- If the second expression is a numeric value, we add the two values
                            OK (Numeric v2) s2 -> OK (Numeric (v1 + v2)) s2
                            -- If the second expression is a boolean value, we return an error
                            OK (Boolean v2) s2 -> Error
                            Error -> error (display (m, j) ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)
                                        where ((m, j),i,o) = s1
    -- If the first expression is a boolean value, we return an error
    OK (Boolean v1) s1 -> error (display m ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)
                                        where (m,i,o) = s1
    Error -> error (display (m, j) ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)
                where ((m, j),i,o) = s 

-- Assignment statements perform a memory updating operation.
-- A memory is represented as a function which returns the
-- value of an identifier.   To update a memory with a new
-- identifier-value mapping, we return a function that will
-- return the value if given the identifier or will use the
-- original memory function to retrieve values associated with
-- other identifiers.

searchMem _ [] = False
searchMem n (x:xs)
  | n == x = True
  | otherwise = searchMem n xs

update (m, j) ide val =
  let newMem = if searchMem ide m then m else ide : m
      newJ ide2 = if ide == ide2 then Stored val else j ide2
  in (newMem, newJ)

-- We will later need a function to initialize an "empty" memory
-- that returns Unbound for every identifier.

emptyMem ide = Unbound

cmd_semantics (Assign ident exp) s =
  case (exp_semantics exp s) of
    OK v1 ((m1, n1), i1, o1) -> OKc (update (m1, n1) ident v1, i1, o1)
    Error -> Errorc

cmd_semantics (Output exp) s =
  case (exp_semantics exp s) of
    OK v1 ((m1, n1), i1, o1) -> OKc ((m1, n1), i1, o1 ++ [v1])
    Error -> Errorc

-- Semantics of the 'IfThenElse' expression
cmd_semantics (IfThenElse exp cmd1 cmd2) s =
    case (exp_semantics exp s) of
        -- If the expression is a boolean with a value of True, we evaluate the command cmd1
        OK (Boolean True) s1 -> cmd_semantics cmd1 s1
        -- If the expression is a boolean with a value of False, we evaluate the command cmd2
        OK (Boolean False) s1 -> cmd_semantics cmd2 s1
        -- If the expression is a numeric value, we return an error
        OK (Numeric v) s1 -> Errorc
        Error -> Errorc

-- Semantics of the 'WhileDo' expression
cmd_semantics (WhileDo exp cmd) s = 
    case (exp_semantics exp s) of
    -- If the expression is a boolean with a value of True, we evaluate the command cmd and then evaluate the while loop again
    OK (Boolean True) s1 -> cmd_semantics (Seq cmd (WhileDo exp cmd)) s1
    -- If the expression is a boolean with a value of False, we return the state
    OK (Boolean False) s1 -> OKc s1
    -- If the expression is a numeric value, we return an error
    OK (Numeric v) s1 -> Errorc
    Error -> Errorc


cmd_semantics (Seq cmd1 cmd2) s =
  case (cmd_semantics cmd1 s) of
    OKc s1 -> cmd_semantics cmd2 s1
    Errorc -> Errorc

--  4.  Demo/Semantic Change/Demo

-- To demo the semantics in action, we use the following
-- "run" function to execute a TINY program for a given input.
-- (Note that the memory is initialized to empty, as is the output).

run program input =
  case (cmd_semantics parsed_program (([], emptyMem), input, [])) of
    OKc ((m, j), i, o) -> o
    Errorc -> [ERROR]
  where parsed_program = cparse program


-- Test programs

-- Test data---the programs first, second, third, fourth and fifth are as in the module TINYParser

-- For first 

input1 = [Numeric 1, Numeric 2]

input2 = [Numeric 1, Numeric 3]

input3 = [Boolean True, Numeric 2]

--- For second, which is gordon

input4 =  [Numeric 1, Numeric 2, Boolean True]

input5 =  [Numeric 1, Numeric 2, Numeric 3, Boolean True]

-- For third, fourth and fifth we need just a single number input

-- testprog6 for generating errors

testprog6 = "y := 1; y := y = x"

-- so try

--    run testprog6 [ ]
 
-- to see the error reporting