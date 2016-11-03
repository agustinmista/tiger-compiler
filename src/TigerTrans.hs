{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module TigerTrans where

import qualified Control.Monad.State as ST
import           Prelude             hiding (EQ, GT, LT, error, exp, seq)
import qualified Prelude             as P (error)
import qualified TigerAbs            as Abs
import           TigerEnv
import           TigerErrores
import           TigerFrame          as F
import           TigerTemp
import           TigerTree

import           Control.Monad
import qualified Data.Foldable       as Fold
import           Data.List           as List
import           Data.Ord            hiding (EQ, GT, LT)

import qualified Data.Text           as T

import           Debug.Trace

type TransFrag = Frag -- Reexport Fragtype

data BExp = Ex Exp | Nx Stm | Cx ((Label, Label) -> Stm)

instance Show BExp where
    show (Ex e) = "Ex " ++ show e
    show (Nx e) = "Nx " ++ show e
    show (Cx _ ) = "Cx "

type Level = [(Frame, Int)]

getFrame :: Level -> Frame
getFrame ((f,_):_) = f

getNlvl :: Level -> Int
getNlvl ((_,i):_) = i

setFrame :: Frame -> Level -> Level
setFrame f ((_,l):xs) = (f,l) : xs

newLevel :: Level -> T.Text -> [Bool] -> Level 
newLevel [] s bs = [(newFrame s bs,0)]
newLevel ls@((pF,lvl):_) s bs = (newFrame s bs, lvl+1) : ls
--In the semantic analysis phase of the Tiger compiler, transDec
--creates a new "nesting level" for each function by calling
--newLevel


getParent :: Level -> Level
getParent [] = P.error "No fuimos del outermost level"
getParent (_:xs) = xs

outermost :: Level
outermost = [(newFrame (T.pack "_undermain") [],-1) ]


class (Monad w, TLGenerator w, Daemon w) => FlorV w where --Acá hay que completar algunas funciones
    -- |Level managment
    getActualLevel :: w Int
    upLvl :: w ()
    downLvl :: w ()
    -- | Salida managment
    pushSalida :: Maybe Label -> w ()
    topSalida :: w (Maybe Label)
    popSalida :: w()
    -- |Level managment Cont.
    pushLevel :: Level -> w ()
    popLevel  :: w ()
    topLevel  :: w Level
    allocLocal :: Bool -> w Access
    allocLocal b = do
        t <- topLevel
        popLevel
        (f,acc) <- F.allocLocal (getFrame t) b
        let nt = setFrame f t
        pushLevel nt
        return  acc
    allocArg :: Bool -> w Access
    allocArg b = do
        t <- topLevel
        popLevel
        (f,a) <- F.allocArg (getFrame t) b
        pushLevel (setFrame f t)
        return a
    -- | Frag managment
    pushFrag  :: Frag -> w ()
    getFrags  :: w [Frag]


class IrGen w where
    procEntryExit :: Level -> BExp -> w ()
    unitExp :: w BExp
    nilExp :: w BExp
    intExp :: Int -> w BExp
    stringExp :: T.Text -> w BExp
    simpleVar :: Access -> Int -> w BExp
    varDec :: Access -> w BExp
    fieldVar :: BExp -> Int -> w BExp
    subscriptVar :: BExp -> BExp -> w BExp
    recordExp :: [(BExp,Int)]  -> w BExp -- Falta completar
    callExp :: Label -> Bool -> Bool -> Level -> [BExp] -> w BExp --Hay que revisarla
    letExp :: [BExp] -> BExp -> w BExp
    breakExp :: w BExp
    seqExp :: [BExp] -> w BExp
    preWhileforExp :: w ()
    posWhileforExp :: w ()
    whileExp :: BExp -> BExp -> w BExp
    forExp :: BExp -> BExp -> BExp -> BExp -> w BExp
    ifThenExp :: BExp -> BExp -> w BExp
    ifThenElseExp :: BExp -> BExp -> BExp -> w BExp
    ifThenElseExpUnit :: BExp -> BExp -> BExp -> w BExp --Falta completar
    assignExp :: BExp -> BExp -> w BExp 
    preFunctionDec :: Level -> w ()
    posFunctionDec :: w ()
    functionDec :: BExp -> Level -> Bool -> w BExp
    binOpIntExp :: BExp -> Abs.Oper -> BExp -> w BExp --Falta completar
    binOpIntRelExp :: BExp -> Abs.Oper -> BExp -> w BExp --Falta completar
    binOpStrExp :: BExp -> Abs.Oper -> BExp -> w BExp --Falta completar
    arrayExp :: BExp -> BExp -> w BExp



-- Esta funcion sirve para calcular los saltos de frames
preSL :: (Monad w, TLGenerator w)  => Int -> Temp -> w [Stm]
preSL 0 _ = return [] 
preSL d t = do 
        return $ [ Move (Temp t) (Binop Plus (Temp t) (Const fpPrevLev))
                 , Move (Temp t) (Mem (Temp t)) ]

staticL :: (Monad w, TLGenerator w) => Int -> Int -> w Exp
staticL caller callee
    | caller >  callee  = return $ Temp fp
    | caller == callee  = return $ Mem (Binop Plus (Temp fp) (Const fpPrevLev)) 
    | otherwise = do
        t <- newTemp
        jumps <- preSL (callee - caller) t
        return $ Eseq (seq $
            [ Move (Temp t) (Temp fp) ] ++ jumps) (Temp t)  

accumEffects :: (Monad w, TLGenerator w) => ([Exp], [Stm]) -> BExp -> w ([Exp], [Stm])
accumEffects (tmp, eff) (Ex (Const n)) = return (Const n:tmp, eff)
accumEffects (tmp, eff) (Ex (Name n))  = return (Name n:tmp, eff)
accumEffects (tmp, eff) (Ex (Temp n))  = return (Temp n:tmp, eff)
accumEffects (tmp, eff) h = do
    t  <- newTemp
    h' <- unEx h
    return (Temp t:tmp, (Move (Temp t) h'):eff)

seq :: [Stm] -> Stm
seq [] = ExpS $ Const 0
seq [s] = s
seq (x:xs) = Seq x (seq xs)

unEx :: (Monad w,TLGenerator w) => BExp -> w Exp
unEx (Ex e) = return e
unEx (Nx s) = return $ Eseq s (Const 0)
unEx (Cx cf) = do
    r <- newTemp
    t <- newLabel
    f <- newLabel
    return $ Eseq
        (seq [
            Move (Temp r) (Const 1),
            cf(t,f),
            Label f,
            Move (Temp r) (Const 0),
            Label t])
        (Temp r)


unNx :: (Monad w,TLGenerator w) => BExp -> w Stm
unNx (Ex e) = return $ ExpS e
unNx (Nx s) = return s
unNx (Cx cf) = do
        t <- newLabel
        f <- newLabel
        return $ seq [cf(t,f),Label t, Label f]

unCx :: (Monad w,TLGenerator w, Daemon w) => BExp -> w ((Label, Label) -> Stm)
unCx (Nx s) = error $ internal $ strToErr "UnCx(Nx...)"
unCx (Cx cf) = return cf
unCx (Ex (Const 0)) = return (\(_,f) -> Jump (Name f) f)
unCx (Ex (Const _)) = return (\(t,_) -> Jump (Name t) t)
unCx (Ex e) = return (uncurry (CJump NE e (Const 0)))

instance (FlorV w) => IrGen w where

    procEntryExit lvl bd =  do
        bd' <- unNx bd
        let res = Proc bd' (getFrame lvl)
        pushFrag res

    stringExp t = do
        l <- newLabel
        let ln = T.append (T.pack ".long ")  (T.pack $ show $ T.length t)
        let str = T.append (T.append (T.pack ".string \"") t) (T.pack "\"")
        pushFrag $ AString l [ln,str]
        return $ Ex $ Name l

    preFunctionDec lvl = do
        pushSalida Nothing  -- In case a break is called.
        upLvl
        pushLevel lvl

    posFunctionDec = popSalida >> downLvl

    -- functionDec :: BExp -> Level -> Bool -> w BExp
    functionDec bd lvl proc = do
        body <- if proc then unNx bd
                else do
                        e <- unEx bd
                        return $ Move (Temp rv) e
        procEntryExit lvl (Nx body)
        return $ Ex $ Const 0 
    
    simpleVar acc level = do
        actual <- getActualLevel
        return $ Ex $ exp acc (actual - level)


    varDec acc = do { i <- getActualLevel; simpleVar acc i}

    unitExp = return $ Ex (Const 0)

    nilExp = return $ Ex (Const 0)

    intExp i = return $ Ex (Const i)

    -- fieldVar :: BExp -> Int -> BExp
    fieldVar be i = do -- Ya ha sido chequeado que el indice i es valido 
        evar <- unEx be   -- Desempaquetamos la direccion de be
        tvar <- newTemp   -- Creamos un temporal para guardarla
        return $ Ex $
            Eseq
                (seq    [Move (Temp tvar) evar                         -- Movemos la direccion de be al temporal
                        ,ExpS $ externalCall "_checkNil" [Temp tvar]]) -- Una funcion de runtime chequea que be no sea nil
                (Mem $ Binop Plus (Temp tvar) (Binop Mul (Const i) (Const wSz))) --Retornamos la direccion del campo buscado


    -- subscriptVar :: BExp -> BExp -> w BExp
    subscriptVar var ind = do
        evar <- unEx var
        eind <- unEx ind
        tvar <- newTemp
        tind <- newTemp
        return $ Ex $
            Eseq
                (seq    [Move (Temp tvar) evar
                        ,Move (Temp tind) eind
                        ,ExpS $ externalCall "_checkIndex" [Temp tvar, Temp tind]])
                (Mem $ Binop Plus (Temp tvar) (Binop Mul (Temp tind) (Const wSz)))   
    
    -- recordExp :: [(BExp,Int)]  -> w BExp
    -- pasamos el rv a un temp lo mas rapido posible para que no se pise
    recordExp flds = do
        cflds <- mapM (\(e,i) -> unEx e >>= \be -> return (be,i)) flds
        let scflds = map fst $ sortBy (comparing snd) cflds
        t <- newTemp
        return $ Ex $ Eseq (seq
               [ ExpS $ externalCall "_allocRecord" scflds
               , Move (Temp t) (Temp rv)
               ]) (Temp t)
    
 
    -- callExp :: Label -> Bool -> Bool -> Level -> [BExp] -> w BExp
    -- externa marca si la función llamada es del exterior (cualquiera del runtime)
    -- isproc marca si la función no devuelve valor (f: A -> Unit)
    -- cuando es externa no hay que pasarle el static link
    callExp name external isproc lvl args = do --ver
        actual <- getActualLevel        
        sl <- staticL actual (getNlvl lvl)
        t <- newTemp
        (tmps, effs) <- foldM accumEffects ([],[]) args
        let eargs = if external then tmps else [sl] ++ tmps
        if isproc 
            then return $ Nx $ seq (effs ++ [ExpS $ Call (Name name) eargs])
            else return $ Ex $ Eseq (seq $ effs ++
                    [ ExpS (Call (Name name) eargs)
                    , Move (Temp t) (Temp rv)]) (Temp t)
    
    -- letExp :: [BExp] -> BExp -> w BExp
    letExp [] e = do -- Puede parecer al dope, pero no...
            e' <- unEx e
            return $ Ex e'
    letExp bs body = do
        bes <- mapM unNx bs
        be <- unEx body
        return $ Ex $ Eseq (seq bes) be

    -- breakExp :: w BExp
    breakExp = do
        lfin <- topSalida
        case lfin of
            Just fin -> return $ Nx $ Jump (Name fin) fin
            Nothing  -> error $ internal $ T.pack "\tBreak fuera de loop"
            
    -- seqExp :: [BExp] -> w BExp
    seqExp [] = return $ Nx $ ExpS $ Const 0
    seqExp bes = do
        let ret = last bes
        case ret of
            Nx e' -> do
                bes' <- mapM unNx bes
                return $ Nx $ seq bes'
            Ex e' -> do
                    let bfront = init bes
                    ess <- mapM unNx bfront
                    return $ Ex $ Eseq (seq ess) e'
            _ -> error $ internal $ T.pack "WAT!123"

    -- preWhileforExp :: w ()
    preWhileforExp = do
        l <- newLabel
        pushSalida (Just l)

    -- posWhileforExp :: w ()
    posWhileforExp = popSalida

    -- whileExp :: BExp -> BExp -> Level -> w BExp
    whileExp cond body = do
        test <- unCx cond
        cody <- unNx body
        init <- newLabel
        bd <- newLabel
        lastM <- topSalida
        case lastM of
            Just last ->
                return $ Nx $ seq
                    [Label init
                    , test (bd,last)
                    , Label bd
                    , cody
                    , Jump (Name init) init
                    , Label last]
            _ -> error $ internal $ T.pack "no label in salida"

    -- forExp :: BExp -> BExp -> BExp -> BExp -> w BExp
    forExp lo hi var body = do
       lcond <- newLabel
       lbody <- newLabel
       ltop  <- topSalida
       last  <- maybe (error $ internal $ T.pack "no label in salida") return ltop
       clo   <- unEx lo
       chi   <- unEx hi
       cvar  <- unEx var
       cbody <- unNx body
       case chi of 
           Const i -> return $ Nx $ seq --TODO: Agrupar los seq en uno solo
                         [ Move cvar clo
                         , Jump (Name lcond) lcond
                         , Label lbody
                         , cbody
                         , Move cvar (Binop Plus cvar (Const 1))
                         , Label lcond
                         , CJump GT cvar (Const i) last lbody --Falla con entero mas grande
                         , Label last]
           _       -> do
                         tmp <- newTemp
                         return $ Nx $ seq 
                           [ Move cvar clo
                           , Move (Temp tmp) chi
                           , Jump (Name lcond) lcond
                           , Label lbody
                           , cbody
                           , Move cvar (Binop Plus cvar (Const 1))
                           , Label lcond
                           , CJump GT cvar (Temp tmp) last lbody --Falla con entero mas grande
                           , Label last]

    -- ifThenExp :: BExp -> BExp -> w BExp
    ifThenExp cond bod = do
       test  <- unCx cond
       cthen <- unEx bod
       lthen <- newLabel 
       lend  <- newLabel
       tmp <- newTemp
       return $ Ex $ Eseq (seq
            [ test (lthen, lend)
            , Label lthen, Move (Temp tmp) cthen   
            , Label lend
            ]) (Temp tmp)
    
    -- ifThenElseExp :: BExp -> BExp -> BExp -> w BExp
    ifThenElseExp cond bod els = do
        test  <- unCx cond
        cthen <- unEx bod
        celse <- unEx els
        lthen <- newLabel 
        lelse <- newLabel
        lend  <- newLabel
        tmp <- newTemp
        return $ Ex $ Eseq (seq
            [ test (lthen, lelse)
            , Label lthen, Move (Temp tmp) cthen, Jump (Name lend) lend   
            , Label lelse, Move (Temp tmp) celse
            , Label lend
            ]) (Temp tmp)

    -- ifThenElseExpUnit :: BExp -> BExp -> BExp -> w BExp
    ifThenElseExpUnit _ _ _ = P.error "ifThenElseExpUnit"

    -- assignExp :: BExp -> BExp -> w BExp
    assignExp cvar cinit = do
        cvara <- unEx cvar
        cin <- unEx cinit
        case cvara of
            Mem v' ->  do
                t <- newTemp
                return $ Nx $ seq [Move (Temp t) cin, Move cvara (Temp t)]
            _ -> return $ Nx $ Move cvara cin

    -- binOpIntExp :: BExp -> Abs.Oper -> BExp -> w BExp
    binOpIntExp le op re = do 
        l <- unEx le
        r <- unEx re
        let condJmpFunc oper = \(t,f) -> CJump oper l r t f
            jmpFunc True  =  \(t,_) -> Jump (Name t) t 
            jmpFunc False =  \(_,f) -> Jump (Name f) f
        return $ case (l,r,op) of 
            (Const li, Const ri, Abs.PlusOp)   -> Ex $ Const (li+ri)
            (Const li, Const ri, Abs.MinusOp)  -> Ex $ Const (li-ri)
            (Const li, Const ri, Abs.TimesOp)  -> Ex $ Const (li*ri)
            (Const li, Const ri, Abs.DivideOp) -> Ex $ if ri == 0 then Binop Div l r else Const (div li ri)
            (Const li, Const ri, Abs.EqOp)  -> Cx $ jmpFunc (li == ri)  -- Esta es una optimizacion
            (Const li, Const ri, Abs.NeqOp) -> Cx $ jmpFunc (li /= ri)  -- que calcula el salto en tiempo
            (Const li, Const ri, Abs.LtOp)  -> Cx $ jmpFunc (li <  ri)  -- de compilacion, cuando ambos 
            (Const li, Const ri, Abs.LeOp)  -> Cx $ jmpFunc (li <= ri)  -- lados de la operacion son constantes
            (Const li, Const ri, Abs.GtOp)  -> Cx $ jmpFunc (li >  ri)  --
            (Const li, Const ri, Abs.GeOp)  -> Cx $ jmpFunc (li >= ri)  -- 
            (_,_,Abs.PlusOp)   -> Ex $ Binop Plus l r
            (_,_,Abs.MinusOp)  -> Ex $ Binop Minus l r
            (_,_,Abs.TimesOp)  -> Ex $ Binop Mul l r
            (_,_,Abs.DivideOp) -> Ex $ Binop Div l r
            (_,_,Abs.EqOp)     -> Cx $ condJmpFunc EQ
            (_,_,Abs.NeqOp)    -> Cx $ condJmpFunc NE
            (_,_,Abs.LtOp)     -> Cx $ condJmpFunc LT
            (_,_,Abs.LeOp)     -> Cx $ condJmpFunc LE
            (_,_,Abs.GtOp)     -> Cx $ condJmpFunc GT
            (_,_,Abs.GeOp)     -> Cx $ condJmpFunc GE
    
    -- binOpIntRelExp :: BExp -> Abs.Oper -> BExp -> w BExp 
    binOpIntRelExp strl op strr = return $ Ex $ Const 0

    -- binOpStrExp :: BExp -> Abs.Oper -> BExp -> w BExp
    binOpStrExp strl op strr = do
        l <- unEx strl
        r <- unEx strr
        t <- newTemp
        let strCmpExp = Eseq (seq [ ExpS $ externalCall "_stringCompare" [l,r]
                                  , Move (Temp t) (Temp rv)]) (Temp t) 
            condJmpFunc oper = \(t,f) -> CJump oper strCmpExp (Const 0) t f
        case op of
            Abs.EqOp  -> return $ Cx $ condJmpFunc EQ
            Abs.NeqOp -> return $ Cx $ condJmpFunc NE
            Abs.LtOp  -> return $ Cx $ condJmpFunc LT
            Abs.LeOp  -> return $ Cx $ condJmpFunc LE
            Abs.GtOp  -> return $ Cx $ condJmpFunc GT
            Abs.GeOp  -> return $ Cx $ condJmpFunc GE
            _ -> error $ internal $ T.pack $ "la operacion " ++ show op ++ " no esta permitida para strings"
    
    -- arrayExp :: BExp -> BExp -> w BExp
    arrayExp size init = do
        sz <- unEx size
        ini <- unEx init
        t <- newTemp
        return $ Ex $ Eseq (seq
                [ExpS $ externalCall "_allocArray" [sz,ini]
                , Move (Temp t) (Temp rv)
                ]) (Temp t)

