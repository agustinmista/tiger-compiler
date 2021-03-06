module TigerFrame where

import TigerTemp
import TigerTree 
import Prelude hiding (exp)

import qualified Data.Text as T
--


-- | Frame pointer
fp :: Temp
fp = pack "FP"

-- | Stack pointer
sp :: Temp
sp = pack "SP"

-- | Return value
rv :: Temp
rv = pack "RV"

-- | Word size in bytes
wSz :: Int
wSz = 4
-- | Base two logarithm of word size in bytes
log2WSz :: Int
log2WSz = 2

-- | Offset
fpPrev :: Int
fpPrev = 0
-- | Offset
fpPrevLev :: Int
fpPrevLev = wSz

argsGap = wSz
localsGap = 4

argsInicial = 0
regInicial = 1
localsInicial = 1 * wSz 

calldefs = [rv]
specialregs = [rv, fp, sp]

data Access = InFrame Int | InReg Temp  -- inFrame(X) : localización a offset X del fp ; InReg("r"): localización en el registro r
    deriving Show
data Frag = Proc Stm Frame | AString Label [T.Text]

sepFrag :: [Frag] -> ([Frag],[(Stm,Frame)])
sepFrag xs = (reverse ass, reverse stmss)
    where
        (ass, stmss) = foldl (\ (lbls,stms) x ->
            case x of
                Proc st fr -> (lbls, (st,fr) : stms)
                AString {} -> (x:lbls, stms)
                ) ([],[]) xs

instance Show Frag where
    show (Proc s f) = "Frame:" ++ show f ++ '\n': show s
    show (AString l ts) = show l ++ ":\n" ++ (foldr (\t ts -> ("\n\t" ++ T.unpack t) ++ ts) "" ts)

data Frame = Frame 
    { name :: T.Text
    , formals :: [Bool]
    , locals :: [Bool]
    , actualArg :: Int
    , actualLocal :: Int    
    , actualReg :: Int
    } deriving Show

defaultFrame :: Frame
defaultFrame =  Frame 
    { name = T.empty
    , formals = []
    , locals = []
    , actualArg = argsInicial
    , actualLocal = localsInicial
    , actualReg = regInicial }

-- TODOS A stack por i386
prepFormals :: Frame -> [Access]
prepFormals fs = reverse $ snd (foldl (\ (n,rs) _ -> (n+argsGap, InFrame n : rs) ) (argsInicial,[]) (formals fs))

newFrame :: T.Text -> [Bool] -> Frame
newFrame nm fs = defaultFrame { name = nm, formals = fs }

externalCall :: String -> [Exp] -> Exp
externalCall s = Call (Name $ T.pack s) 

allocArg :: (TLGenerator w) => Frame -> Bool -> w (Frame, Access)
allocArg fr True =   
    let actual = actualArg fr 
        acc = InFrame $ actual + argsGap in
    return (fr{actualArg = actual+1}, acc)
allocArg fr False = do
    s <- newTemp
    return (fr, InReg s)


--allocLocal f true  aloca una nueva variable local en un frame f. Esto retorna donde la guardo (Access)
--el booleano indica si la nueva variable esta escapada o no.
allocLocal :: (TLGenerator w) => Frame -> Bool -> w (Frame, Access)
allocLocal fr True = 
    let actual = actualLocal fr 
        acc = InFrame $ actual + localsGap in
    return (fr{actualLocal= actual +1}, acc)
allocLocal fr False = do
    s <- newTemp
    return (fr, InReg s)

auxexp :: Int -> Exp
auxexp 0 = Temp fp
auxexp n = Mem(Binop Plus (auxexp (n-1)) (Const fpPrevLev))

exp :: Access -> Int -> Exp
exp (InFrame k) e = Mem(Binop Plus (auxexp e) (Const k))
exp (InReg l) _ = Temp l
