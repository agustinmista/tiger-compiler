{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances,
TypeFamilies, MultiParamTypeClasses #-}
module TigerInterp where

--import TigerFrame
import Data.Map.Strict
import TigerTree as Tree
import TigerTemp hiding (pack)
import Data.Text as T hiding (empty)
import qualified TigerFrame as F
import TigerEnv

import Data.Stream as Str
import Data.Char
import Data.Bits
import Prelude as P hiding (lookup, putStr)

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State

type Mem = Int
type Args = [Int]

data Intra = Intra {
         input :: Stream String
        ,regs :: [Mapper Mach Temp Int]
        ,nmem :: Int
        ,mem :: Mapper Mach Mem Int
        ,lbl :: Mapper Mach Label Int
        ,funcs :: Mapper Mach Label ([Stm], F.Frame)
    }

--type Mach = State Intra
type Mach = WriterT String (State Intra)

instance Environmental Mach where
    data Mapper Mach a b = MM (Map a b)
    lookupI a (MM m) = lookup a m
    insertI k v (MM m) = MM $ insert k v m
    intersecI f (MM m1) (MM m2) = MM (intersectionWith f m1 m2)
    updateI = insertI
    emptyI = MM empty

class (Monad w)=> Machine w where
    getStr :: w String
    putStr :: String -> w ()
    -- Save/Restore Points
    setRestorePoint :: w ()
    restorePoint :: w ()
    -- Temp management
    loadTemp :: Temp -> w Int 
    storeTemp :: Temp -> Int -> w ()
    printTemps :: w ()
    -- Mem management
    newMem :: Int -> w Int -- newMem n = n * wSz 
    loadMem :: Mem -> w Int
    storeMem :: Mem -> Int -> w ()
    printMems :: w ()
    -- Label management
    loadLabel :: Label -> w Int
    storeLabel :: Label -> Int -> w ()
    -- String Management
    loadString :: Mem -> w Text
    storeString :: Text -> w Mem
    printString :: Mem -> w a
    -- Error Handlers?
    abort :: Text -> w a
    -- Function Env
    addFun :: Label -> ([Stm], F.Frame) -> w ()
    getFun :: Label -> w ([Stm],F.Frame)
    callRuntime :: Label -> w (Args -> w a)
    isRuntime :: Label -> w Bool

initArray :: (Machine w) => [Int] -> w Mem
initArray (size : init : rs) = do
    m <- newMem size
    let l = (m+1, size) :  P.zipWith (\ n i -> (m+n*F.wSz,i)) [1..] (P.replicate size init)
    mapM_ (uncurry storeMem) l
    return m
initArray _ = abort $ pack "No debería pasar || initArray"

checkIndexArray :: (Machine w) => Args -> w Int
checkIndexArray (arr : idx : rs) = do
    s <- loadMem (arr + 1) -- Get the size.
    if idx >= s || idx < 0 then
        abort $ pack "Indice fuera de rango"
    else
        return 0
checkIndexArray _ = abort $ pack "No debería pasar || checkIndexArray"

allocRecord :: (Machine w) => Args -> w Mem
allocRecord (n : rs) = do
    m <- newMem n
    mapM_ (uncurry storeMem) $ P.zipWith (\i v -> (m+F.wSz*i,v))[0..n-1] rs
    return m

checkNil :: (Machine w) => Args -> w Int
checkNil (r : rs) = 
    if r == 0 then abort $pack "Nil" else return 0

stringCompare :: (Machine w) => Args -> w Int
stringCompare (strPtr1 : strPtr2 : rs) = do
    str1 <- loadString strPtr1
    str2 <- loadString strPtr2
    case compare str1 str2 of
        P.LT -> return (-1)
        P.EQ -> return 0
        P.GT -> return 1

printFun :: (Machine w) => Args -> w Int
printFun (strPtr : rs) = do --printString strPtr >> return 0
    s <- loadString strPtr
    putStr $ T.unpack s
    return 0

flushFun :: (Machine w) => Args -> w Int
flushFun _ = return 0

ordFun :: (Machine w) => Args -> w Int
ordFun (strPtr : rs) = do
    str <- loadString strPtr
    return $ ord $ T.head str

chrFun :: (Machine w) => Args -> w Mem
chrFun (i : rs) = storeString $ pack [chr i]

sizeFun :: (Machine w) => Args -> w Int 
sizeFun (strPtr : rs) = do
    str <- loadString strPtr
    return $ T.length str

substringFun :: (Machine w) => Args -> w Mem
substringFun (strPtr : fst : n : rs) = do
    str <- loadString strPtr
    storeString $ T.take n $ T.drop fst str 

concatFun :: (Machine w) => Args -> w Mem
concatFun (strPtr1 : strPtr2 : rs) = do
    str1 <- loadString strPtr1
    str2 <- loadString strPtr2
    storeString $ append str1 str2

notFun :: (Machine w) => Args -> w Int
notFun (0 : rs) =  return 1
notFun (_ : rs) =  return 0

getstrFun :: (Machine w) => Args -> w Mem
getstrFun _ = do
    s <- getStr
    storeString $ pack s

-- Insert all initial fracs...
-- Insert all runtime functions!
--

opExp :: BOp -> Int -> Int -> Int
opExp Plus l r = l + r
opExp Minus l r = l - r
opExp Mul l r = l * r
opExp Div l r = div l r
opExp And l r = l .&. r
opExp Or l r = l .|. r
opExp LShift l r = shiftL l r
opExp RShift l r = shiftR l r
opExp ARShift l r = error "WAT?!"
opExp XOr l r = xor l r

evalExp :: Machine w => Exp -> w Int 
evalExp (Const t) = return t
evalExp (Name l) = loadLabel l
evalExp (Temp t) = loadTemp t
evalExp (Binop b l r)  = do
        l' <- evalExp l
        r' <- evalExp r
        return $ opExp b l' r'
evalExp (Mem m) = evalExp m >>= loadMem
evalExp (Call (Name l) args) = do
    args' <- mapM evalExp args
    b <- isRuntime l 
    rest <- if b then
                    callRuntime l >>= ($ args')
               else
                    evalFun l args'
    storeTemp F.rv rest
    return rest
evalExp (Eseq s e) = abort $ pack "Debería estar canonizado?"

evalStm :: Machine w => Stm -> w (Maybe Label)
evalStm (Move (Temp t) e) = do
    src <- evalExp e
    storeTemp t src
    return Nothing
evalStm (Move (Mem d) e) = do
    src <- evalExp e
    dst <- evalExp d
    storeMem dst src
    return Nothing
evalStm (Move _ _ ) = abort $ pack "Move de algo raro?"
evalStm (ExpS e) = evalExp e >> return Nothing
evalStm (Jump (Name l) _) = return $ Just l
evalStm (Jump _ _) = abort $ pack "Jump a no-label"
evalStm (CJump rop l r t f) = do
    le <- evalExp l
    re <- evalExp r
    let b = case rop of
                Tree.EQ -> le == re
                NE -> le /= re
                Tree.LT -> le < re
                Tree.GT -> le > re
                LE -> le <= re
                GE -> le >= re
                ULT -> le < re
                UGT -> le > re
                ULE -> le <= re
                UGE -> le >= re
    return $ Just (if b then t else f)
evalStm (Seq _ _ ) = abort $ pack "No esta canonizado?"
evalStm (Label _) =  return Nothing

lookupLabel :: Machine w => Label -> [Stm] -> w [Stm]
lookupLabel l [] = abort $ T.append l (T.pack " --- No está en la función")
lookupLabel l r@(Label y : xs) | l == y = return r
lookupLabel l (_ : xs)  = lookupLabel l xs

exec :: Machine w => [Stm] -> w ()
exec (x:xs) = do
    e <- evalStm x
    case e of
        Just f -> lookupLabel f xs >>= exec
        Nothing -> exec xs

evalFun :: (Machine w) => Label -> Args -> w Int
evalFun name args = do
    (body,frame) <- getFun name
    setRestorePoint 
    -- Acomodamos el fp
    fpPrev <- loadTemp F.fp
    storeTemp F.fp (fpPrev-1024*1024) -- Guille
    -- Ponemos los argumentos donde indican los formals?
    -- Ese 0, es por el nivel... 0 es el fp...
    let fmls = P.map (`F.exp` 0) (F.prepFormals frame)
    let fmlsValues = P.zip fmls args
    mapM_ (\ (x,y) -> case x of
            Temp t -> storeTemp t y
            Mem m -> evalExp m >>= (`storeMem` y)) fmlsValues
    -- Ejecutamos el body?
    exec body
    res <- loadTemp F.rv -- levantamos el rv
    restorePoint -- restauramo
    storeTemp F.rv res 
    return res
