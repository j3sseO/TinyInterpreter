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

type Memory = Ide -> MemVal

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
display m = "x = " ++ show (m "x") ++ ", y = " ++ show (m "y") ++ ", z = " ++ show ( m "z") ++ " "


-- 3. Semantic Equations defining the semantic functions
--     Haskell's equational definition is similar but not
--     identical to the equational style used in the mathematical semantics.

exp_semantics Zero s = OK (Numeric 0) s

exp_semantics One s = OK (Numeric 1) s

exp_semantics TT s = OK (Boolean True) s

exp_semantics FF s = OK (Boolean False) s

exp_semantics Read (m, [], o) = error (display m ++ "Input: " ++ "[] " ++ "Output: " ++ show o)

exp_semantics Read (m, (i:is), o) = OK i (m, is, o)

exp_semantics (I ident) (m, i, o) =
 case (m ident) of
    Stored v  -> OK v (m, i, o)
    Unbound   -> error (display m ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)

-- Semantics of the 'Not' expression
exp_semantics (Not exp) s =
    case (exp_semantics exp s) of
    -- If the expression is a boolean, then we negate it
    OK (Boolean v) s1 -> OK (Boolean (not v)) s1
    -- Else, we return an error
    Error -> error (display m ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)
                where (m,i,o) = s

exp_semantics (Equal exp1 exp2) s =
 case (exp_semantics exp1 s) of
   OK (Numeric v1) s1 -> case (exp_semantics exp2 s1) of 
                           OK (Numeric v2) s2 -> OK (Boolean (v1 == v2)) s2
                           OK (Boolean v2) s2 -> OK (Boolean False) s2
                           Error -> error (display m ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)
                                    where (m,i,o) = s1
   OK (Boolean v1) s1 -> case (exp_semantics exp2 s1) of 
                           OK (Boolean v2) s2 -> OK (Boolean (v1 == v2)) s2
                           OK (Numeric v2) s2 -> OK (Boolean False) s2
                           Error -> error (display m ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)
                                    where (m,i,o) = s1
   Error -> error (display m ++ "Input: " ++ show i ++ " " ++ "Output: " ++ show o)
            where (m,i,o) = s

-- exp_semantics (Plus exp1 exp2) s = For you to do!

-- Assignment statements perform a memory updating operation.
-- A memory is represented as a function which returns the
-- value of an identifier.   To update a memory with a new
-- identifier-value mapping, we return a function that will
-- return the value if given the identifier or will use the
-- original memory function to retrieve values associated with
-- other identifiers.

update m ide val =
 \ide2 -> if ide == ide2 then Stored val else m ide2

-- We will later need a function to initialize an "empty" memory
-- that returns Unbound for every identifier.

emptyMem ide = Unbound

cmd_semantics (Assign ident exp) s =
  case (exp_semantics exp s) of
    OK v1 (m1, i1, o1) -> OKc (update m1 ident v1, i1, o1)
    Error -> Errorc

cmd_semantics (Output exp) s =
  case (exp_semantics exp s) of
    OK v1 (m1, i1, o1) -> OKc (m1, i1, o1 ++ [v1])
    Error -> Errorc

-- cmd_semantics (IfThenElse exp cmd1 cmd2) s = For you to do!

-- cmd_semantics (WhileDo exp cmd) s = For you to do!


cmd_semantics (Seq cmd1 cmd2) s =
  case (cmd_semantics cmd1 s) of
    OKc s1 -> cmd_semantics cmd2 s1
    Errorc -> Errorc

--  4.  Demo/Semantic Change/Demo

-- To demo the semantics in action, we use the following
-- "run" function to execute a TINY program for a given input.
-- (Note that the memory is initialized to empty, as is the output).

run program input =
  case (cmd_semantics parsed_program (emptyMem, input, [])) of
    OKc (m, i, o) -> o
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