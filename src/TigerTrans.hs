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

getParent :: Level -> Level
getParent [] = P.error "No fuimos del outermost level"
getParent (_:xs) = xs

outermost :: Level
outermost = [(newFrame (T.pack "_undermain") [],-1) ]

class (Monad w, TLGenerator w, Daemon w) => FlorV w where
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
    recordExp :: [(BExp,Int)]  -> w BExp
    callExp :: Label -> Bool -> Bool -> Level -> [BExp] -> w BExp
    letExp :: [BExp] -> BExp -> w BExp
    breakExp :: w BExp
    seqExp :: [BExp] -> w BExp
    preWhileforExp :: w ()
    posWhileforExp :: w ()
    whileExp :: BExp -> BExp -> w BExp
    forExp :: BExp -> BExp -> BExp -> BExp -> w BExp
    ifThenExp :: BExp -> BExp -> w BExp
    ifThenElseExp :: BExp -> BExp -> BExp -> w BExp
    ifThenElseExpUnit :: BExp -> BExp -> BExp -> w BExp
    assignExp :: BExp -> BExp -> w BExp
    preFunctionDec :: Level -> w ()
    posFunctionDec :: w ()
    functionDec :: BExp -> Level -> Bool -> w BExp
    binOpIntExp :: BExp -> Abs.Oper -> BExp -> w BExp
    binOpIntRelExp :: BExp -> Abs.Oper -> BExp -> w BExp
    binOpStrExp :: BExp -> Abs.Oper -> BExp -> w BExp
    arrayExp :: BExp -> BExp -> w BExp

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
        trace ("procEntry") $ pushFrag res
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
    simpleVar acc level = error "COMPLETAR"
    varDec acc = do { i <- getActualLevel; simpleVar acc i}
    unitExp = return $ Ex (Const 0)
    nilExp = return $ Ex (Const 0)
    intExp i = return $ Ex (Const i)
    fieldVar be i = error "COMPLETAR"
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
    recordExp flds = error "COMPLETAR"
    -- callExp :: Label -> Bool -> Bool -> Level -> [BExp] -> w BExp
    callExp name external isproc lvl args = error "COMPLETAR"
    -- letExp :: [BExp] -> BExp -> w BExp
    letExp [] e = do -- Puede parecer al dope, pero no...
            e' <- unEx e
            return $ Ex e'
    letExp bs body = do
        bes <- mapM unNx bs
        be <- unEx body
        return $ Ex $ Eseq (seq bes) be
    -- breakExp :: w BExp
    breakExp = error "COMPLETAR"
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
                    , Label last
                    , Jump (Name init) init
                    , Label last]
            _ -> error $ internal $ T.pack "no label in salida"
    -- forExp :: BExp -> BExp -> BExp -> BExp -> w BExp
    forExp lo hi var body = error "COMPLETAR"
    -- ifThenExp :: BExp -> BExp -> w BExp
    ifThenExp cond bod = error "COMPLETAR"
    -- ifThenElseExp :: BExp -> BExp -> BExp -> w BExp
    ifThenElseExp cond bod els = error "COMPLETAR"
    -- ifThenElseExpUnit :: BExp -> BExp -> BExp -> w BExp
    ifThenElseExpUnit _ _ _ = error "COmpletaR?"
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
    binOpIntExp le op re = error "COMPLETAR"
    -- binOpStrExp :: BExp -> Abs.Oper -> BExp -> w BExp
    binOpStrExp strl op strr = error "COMPLETAR"
    -- arrayExp :: BExp -> BExp -> w BExp
    arrayExp size init = do
        sz <- unEx size
        ini <- unEx init
        t <- newTemp
        return $ Ex $ Eseq (seq
                [ExpS $ externalCall "_allocArray" [sz,ini]
                , Move (Temp t) (Temp rv)
                ]) (Temp t)

