{-# LANGUAGE GADTs #-}
module TigerAbs where

import qualified Data.Text as T

type Symbol = T.Text
data Pos = Simple {line::Int, col :: Int} | Range Pos Pos
    deriving Show

printPos :: Pos -> String
printPos (Simple l c) = "(" ++ show l ++","++ show c++")"
printPos (Range b e) = "Entre --" ++ printPos b ++ " | " ++ printPos e 

posToLabel :: Pos -> String
posToLabel (Simple l r) = (show l) ++ '.':(show r)
posToLabel (Range l r) = (posToLabel l) ++ '.':(posToLabel r)

-- | Representamos las variables
data Var where
    -- | Nombre de variable. Por ejemplo '(a+1)', 'a' se representa con una
    -- SimpleVar "a".
    SimpleVar :: Symbol -> Var
    -- | Representa el acceso a un campo particular de un record. Pj: a.pepe.
    -- daría a la construcción de FieldVar (SimpleVar "a") "pepe"
    FieldVar :: Var -> Symbol -> Var
    -- | Representa el acceso a un elemento de un array. Pj: a[(3+4)]. Daría a
    -- la construcción de: SubscriptVar (SimpleVar "a") (OpExp (IntExp 3) PlusOp
    -- (IntExp 4))
    SubscriptVar :: Var -> Exp -> Var
    deriving Show

-- | Tipo que representa las expresiones de tiger! Todos los constructores
-- llevan la posición en la que se encuentra el texto en el código fuente que
-- dio lugar a la construcción del AST.
data Exp where
    -- | Representa una variable, el resultado es otorgar el valor de la
    -- variable.
    VarExp :: Var -> Pos -> Exp
    -- | Unit, no es posible escribir unit en el lenguaje fuente.
    UnitExp :: Pos -> Exp
    -- | Break
    BreakExp :: Pos -> Exp
    -- | Nil
    NilExp :: Pos -> Exp
    -- | Enteros
    IntExp :: Int -> Pos -> Exp
    -- | Cadenas de texto
    StringExp :: String -> Pos -> Exp
    -- | Llamada de una función. Ej: f (45). Daría lugar al sig árbol: CallExp
    -- "f" [IntExp 45] Pos
    CallExp :: Symbol -> [Exp] -> Pos -> Exp
    -- | Operaciones. Ej: 3+4. (OpExp (IntExp 3) PlusOp (IntExp 4))
    OpExp :: Exp -> Oper -> Exp -> Pos -> Exp 
    -- | Records, representa un valor de un tipo record. Pj: lista{hd=1;tail=nil}
    -- nos daría un AST: RecordExp [("hd",IntExp 1),("tail",NilExp)] "lista"
    -- Pos. Recuerden, nos genera un valor de tipo record.
    RecordExp :: [(Symbol, Exp)] -> Symbol -> Pos -> Exp
    -- | SEcuencia de expresiones, el valor debería estar dictado por la ultima.
    -- Ej: 4 ; print("Holis") ;  0. Genera: SeqExp [IntExp 4 Pos,
    -- CallExp "print" [StringExp "Holis"] Pos, IntExp 0 Pos]  Pos
    SeqExp :: [Exp] -> Pos -> Exp
    -- | Asignación. Ej: a := 3. AssignExp (SimpleVar "a") (IntExp 3 Pos) Pos
    AssignExp :: Var -> Exp -> Pos -> Exp
    -- | Condicional. Ej: if 3 then print("pepe"). Genera: IfExp (IntExp 3 Pos)
    -- (CallExp "print" ["pepe"] Pos) NONE Pos
    IfExp :: Exp -> Exp -> Maybe Exp -> Pos -> Exp
    -- | Bucle while. 
    WhileExp :: Exp -> Exp -> Pos -> Exp
    -- | Bucle for. 
    ForExp :: Symbol -> Maybe Bool -> Exp -> Exp -> Exp -> Pos -> Exp
    -- | Expresiones tipo let. Es el único lugar donde pueden declarar nuevas
    -- varibles, tipos y funciones. Ej: let var a := 3 in a end genera el árbol:
    -- LetExp [VarDec "a" Nothing Nothing (IntExp 3 Pos) Pos] (SimpleVar "a")
    -- Pos
    LetExp :: [Dec] -> Exp -> Pos -> Exp
    -- | Representa un valor de tipo Arreglo. Nos define un nuevo valor de tipo
    -- arreglo. Pj: intArray [3+4] of (2*2). Nos genra el árbol: ArrayExp
    -- "intArray" (OpExp (IntExp 3 Pos) PlusOp (IntExp 4 Pos)) (OpExp (IntExp 2
    -- Pos) TimesOp (IntExp 2 Pos)) Pos
    ArrayExp :: Symbol -> Exp -> Exp -> Pos -> Exp
    deriving Show

-- | Declaraciones!
data Dec where
    FunctionDec :: [(Symbol,[Field], Maybe Symbol, Exp, Pos)] -> Dec
    VarDec :: Symbol -> Maybe Bool -> Maybe Symbol -> Exp -> Pos -> Dec
    TypeDec :: [(Symbol, Ty, Pos)] -> Dec
    deriving Show

data Ty = NameTy Symbol | RecordTy [Field] | ArrayTy Symbol
    deriving Show

data Oper = PlusOp | MinusOp | TimesOp | DivideOp | EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp
    deriving Show

type Field = (Symbol, Maybe Bool, Ty)
