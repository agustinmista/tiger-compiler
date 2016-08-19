{-# LANGUAGE GADTs #-}
module TigerAbs where

import qualified Data.Text as T

type Symbol = T.Text
data Pos = Simple {line::Int, col :: Int} | Range Pos Pos
    deriving Show

printPos :: Pos -> String
printPos (Simple l c) = "[L:" ++ show l ++".C:"++ show c++"]"
printPos (Range b e) = "Entre --" ++ printPos b ++ " | " ++ printPos e 


-- printPos :: Pos ->  String
-- printPos (l,c) = 
data Var where
    SimpleVar :: Symbol -> Var
    FieldVar :: Var -> Symbol -> Var
    SubscriptVar :: Var -> Exp -> Var
    deriving Show

data Exp where
    VarExp :: Var -> Pos -> Exp
    UnitExp :: Pos -> Exp
    NilExp :: Pos -> Exp
    IntExp :: Int -> Pos -> Exp
    StringExp :: String -> Pos -> Exp
    CallExp :: Symbol -> [Exp] -> Pos -> Exp
    OpExp :: Exp -> Oper -> Exp -> Pos -> Exp 
    RecordExp :: [(Symbol, Exp)] -> Symbol -> Pos -> Exp
    SeqExp :: [Exp] -> Pos -> Exp
    AssignExp :: Var -> Exp -> Pos -> Exp
    IfExp :: Exp -> Exp -> Maybe Exp -> Pos -> Exp
    WhileExp :: Exp -> Exp -> Pos -> Exp
    ForExp :: Symbol -> Maybe Bool -> Exp -> Exp -> Exp -> Pos -> Exp
    LetExp :: [Dec] -> Exp -> Pos -> Exp
    BreakExp :: Pos -> Exp
    ArrayExp :: Symbol -> Exp -> Exp -> Pos -> Exp
    deriving Show

data Dec where
    FunctionDec :: [(Symbol,[Field], Maybe Symbol, Exp, Pos)] -> Dec
    VarDec :: Symbol -> Maybe Bool -> Maybe Symbol -> Exp -> Pos -> Dec
    TypeDec :: [(Symbol, Ty, Pos)] -> Dec
    deriving Show

data Ty = NameTy Symbol | RecordTy [Field] | ArrayTy Symbol
    deriving Show

data Oper = PlusOp | MinusOp | TimesOp | DivideOp
	| EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp
    deriving Show

type Field = (Symbol, Maybe Bool, Ty)
