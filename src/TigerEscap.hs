{-# LANGUAGE LambdaCase,FlexibleInstances, FlexibleContexts, TypeFamilies,MultiParamTypeClasses #-}
module TigerEscap where

import TigerAbs
import TigerEnv
import TigerErrores
import Prelude hiding (lookup,error)
import qualified Prelude as P (error)
import Data.Maybe
import qualified Data.Map.Strict as M
import Data.Functor.Identity

import qualified Data.Text as T

import Control.Monad.State (get,put)
import qualified Control.Monad.State as ST
import Control.Monad (when)
import Control.Monad.Except

-- Debugging
import Debug.Trace
-- trace :: String -> a -> a

data Errores =  NotFound T.Text
                | Interno T.Text 

instance Show Errores where
    show (NotFound e) = "No se encuentra la variable "++ show e
    show (Interno e) = "Error interno " ++ show e
    
eappend (NotFound e) e1 = NotFound (T.append e e1)
eappend (Interno e) e1 = Interno (T.append e e1)

type Depth = Int
type Dat = (Int , Maybe Bool)
type Env = M.Map Symbol Dat
data Estado = S { lvl :: Int, env :: Env}
    deriving Show

data SEstado = Step { l :: Int, e :: [Env]}
    deriving Show

class (Environmental m, NotFounder m) => Escapator m where
    -- Depth Operators
    depth :: m Depth    
    up :: m ()
    down :: m ()
    -- Env operators
    setEnv :: Mapper m Symbol Dat -> m ()
    getEnv :: m (Mapper m Symbol Dat)
    -- 
    -- Funciones cpor default, o de debugging
    -- debugging
    printEnv :: m () --
    printEnv = return ()
    -- errores
    putNum :: Pos -> Error m -> m a
    putNum ln er = error $ adder er $ (T.pack $ printPos ln)
    raise :: Error m -> m a
    raise = error 
    --- 
    update :: Symbol -> Maybe Bool -> m ()
    update s mb = do
        m <- getEnv
        case lookupI s m of
             Nothing -> raise (notfound s)
             (Just (l,_)) -> setEnv (insertI s (l,mb) m)
    lookup :: Symbol -> m (Maybe (Int, Maybe Bool))
    lookup s = do
        m <- getEnv
        return $ lookupI s m
    insert :: Symbol -> Maybe Bool -> m (Mapper m Symbol Dat)
    insert s mb = do
        old <- getEnv
        lvl <- depth
        setEnv (insertI s (lvl,mb) old)
        return old
    updateEnv :: Mapper m Symbol Dat -> m ()
    updateEnv m = do
        actual <- getEnv
        let newEnv = intersecI (\ (olvl, oesc) (nlvl,nesc) -> if olvl == nlvl then (olvl, nesc) else (olvl,oesc)) m actual
        setEnv newEnv

type Stepper = ST.StateT SEstado (Either Errores)

instance Deamon Stepper where
    data Error Stepper = StE Errores
    error (StE e) = throwError e
    handle m f = catchError m (f . StE) 
    internal = StE . Interno
    adder (StE e) e1 = StE (eappend e e1)

instance NotFounder Stepper where
    notfound = StE . NotFound

instance Environmental Stepper where
    data Mapper Stepper a b = MST (M.Map a b)
    emptyI = MST M.empty
    insertI s d (MST e) = MST $ M.insert s d e
    updateI s d (MST e) = MST $ M.insert s d e
    lookupI s (MST e) = M.lookup s e
    intersecI f (MST m1) (MST m2) = MST $ M.intersectionWith f m1 m2

instance Escapator Stepper where
    depth = do
        s <- ST.get
        return (l s)
    up = do
        (Step lvl env) <- ST.get
        ST.put (Step (lvl+1) env) 
    down = do
        (Step lvl env) <- ST.get
        ST.put (Step (lvl-1) env) 
    setEnv (MST e) = do
        (Step lvl xs) <- get
        put (Step lvl (e:xs))
    getEnv = do
        (Step _ (e:es)) <- ST.get
        return (MST e)
    printEnv = do
        (Step l env) <- ST.get
        return (trace ("Entorno(" ++ show l ++")" ++ show env ++ "*****\n") ())
    

type Completor = ST.StateT Estado (Either Errores)

instance Deamon Completor where
    data Error Completor = E Errores
    error (E e) = throwError e
    handle m f = catchError m (f . E) 
    internal = E . Interno
    adder (E e) e1 = E (eappend e e1)

instance NotFounder Completor where
    notfound = E . NotFound


instance Environmental Completor where
    data Mapper Completor a b = M (M.Map a b)
    emptyI = M M.empty
    insertI s d (M e) = M $ M.insert s d e
    updateI s d (M e) = M $ M.insert s d e
    lookupI s (M e) = M.lookup s e
    intersecI f (M m1) (M m2) = M $ M.intersectionWith f m1 m2

instance Escapator Completor where
    depth = do
        s <- ST.get
        return (lvl s)
    up = do
        (S lvl env) <- ST.get
        ST.put (S (lvl+1) env) 
    down = do
        (S lvl env) <- ST.get
        ST.put (S (lvl-1) env) 
    setEnv (M e) = do
        (S lvl _) <- get
        put (S lvl e)
    getEnv = do
        (S _ e) <- get
        return (M e)
    printEnv = do
        (S l env) <- get
        return (trace ("Entorno(" ++ show l ++")" ++ show env ++ "*****\n") ())

type Simpler= ST.State Estado -- Sin manejo de Errores...

instance Deamon Simpler where
    data Error Simpler = Erpes T.Text 
    error (Erpes s) = P.error $ T.unpack s
    internal s = Erpes $ T.pack $ "Interno:" ++ T.unpack s
    handle m err = m -- no se maneja esto..
    adder (Erpes e) e1 = Erpes (T.append e e1)

instance NotFounder Simpler where
    notfound s = Erpes $ T.pack $ "No se encontro :" ++ T.unpack s

instance Environmental Simpler where
    data Mapper Simpler a b = Er (M.Map a b)
    emptyI = Er M.empty
    insertI s d (Er e) = Er $ M.insert s d e
    updateI s d (Er e) = Er $ M.insert s d e
    lookupI s (Er e) = M.lookup s e
    intersecI f (Er m1) (Er m2) = Er $ M.intersectionWith f m1 m2

instance Escapator Simpler where -- No error
    depth = do
        s <- ST.get
        return (lvl s)
    up = do
        (S lvl env) <- ST.get
        ST.put (S (lvl+1) env) 
    down = do
        (S lvl env) <- ST.get
        ST.put (S (lvl-1) env) 
    setEnv (Er e) = do
        (S lvl _) <- get
        put (S lvl e)
    getEnv = do
        (S _ e) <- get
        return (Er e)
    printEnv = do
        (S l env) <- get
        return (trace ("Entorno(" ++ show l ++")" ++ show env ++ "*****\n") ())

-- do 
-- a 
-- b
-- a >>= \t -> b t


travVar :: (Escapator m) => Var -> m Var
travVar (SimpleVar s) = do
    s' <- lookup s
    actLvl <- depth
    case s' of
        Nothing -> raise (notfound s)
        Just (lvl, esc) -> when (actLvl > lvl) $ update s (Just True)
    return (SimpleVar s)
travVar (FieldVar v p) = do
    v' <- travVar v -- v._
    return (FieldVar v' p)
travVar (SubscriptVar v e) = do
        v' <- travVar v
        e' <- travExp e
        return (SubscriptVar v' e')

travExp :: (Escapator m) => Exp -> m Exp 
travExp (VarExp v p) = do
    v' <- handle (travVar v) (putNum p)
    return (VarExp v' p)
travExp (CallExp s args p) = do
    args' <- mapM travExp args
    return (CallExp s args' p)
travExp (OpExp l op r p) = do
    l' <- travExp l
    r' <- travExp r
    return (OpExp l' op r' p)
travExp (RecordExp es s p) = do
    es' <- mapM (\(s,e) -> do
                                e' <- travExp e
                                return (s,e')) es
    return (RecordExp es' s p)
travExp (SeqExp es p) = do
    es' <- mapM travExp es
    return (SeqExp es' p)
travExp (AssignExp v e p) = do
    v' <- handle (travVar v) (putNum p)
    e' <- travExp e
    return (AssignExp v' e' p)
travExp (IfExp c t Nothing p) = do
    c' <- travExp c
    t' <- travExp t
    return (IfExp c' t' Nothing p)
travExp (IfExp c t (Just e) p) = do
    c' <- travExp c
    t' <- travExp t
    e' <- travExp e
    return (IfExp c' t' (Just e') p)
travExp (WhileExp c b p) = do
    c' <- travExp c
    b' <- travExp b
    return (WhileExp c' b' p)
travExp (ForExp s e lo hi body p) = do
    lo' <- travExp lo
    hi' <- travExp hi
    old <- insert s e 
    body' <- travExp body
    setEnv old
    return (ForExp s e lo' hi' body' p)
travExp (LetExp ds e p) = do
    old <- getEnv  -- Security Measures <--
    ds' <- mapM travDecs ds
    e' <- travExp e 
    ds'' <- mapM (\case 
                    (VarDec name _ typ exp p) -> do
                        chk <- lookup name
                        case chk of
                            Nothing -> raise (internal $ T.pack $ "666+1 -- Linea:" ++ show p)
                            Just (_,esc) ->
                                let newvardec = VarDec name esc typ exp p in
                                 return newvardec
                    l -> return l) ds' 
    updateEnv old
    return (LetExp ds'' e' p)
travExp (ArrayExp typ size init p) = do
    s' <- travExp size
    init' <- travExp init 
    return (ArrayExp typ s' init' p)
travExp v = return v

travF :: (Escapator m) => (Symbol,[Field], Maybe Symbol, Exp, Pos) -> m (Symbol,[Field], Maybe Symbol, Exp, Pos)
travF (name, params, res, body, p) = do
    old <- getEnv
    mapM_ (\(name, esc, typ) -> insert name esc) params 
    body' <- travExp body
    params' <- mapM (\(s,_,ty) -> do
                                mb <- lookup s
                                case mb of
                                    Nothing -> raise (internal $ T.pack $ "666+2 -- Linea:" ++ show p)
                                    Just (_,esc) -> return (s,esc,ty)) params
    updateEnv old
    return (name, params', res, body', p)
travDecs ::  (Escapator m) => Dec -> m Dec
travDecs (FunctionDec ls) = do
    up -- New level!! 
    ls' <- mapM travF ls
    down -- Return to old lvl
    return (FunctionDec ls')
travDecs (VarDec name esc typ init p) = do
    init' <- travExp init
    insert name esc
    return (VarDec name esc typ init' p)
travDecs l = return l

initialSt :: Estado
initialSt = S 1 M.empty

calcularEsc :: Exp -> Exp
calcularEsc e = ST.evalState (travExp e) initialSt

showEnv :: Exp -> (Exp,Estado)
showEnv e = ST.runState (travExp e) initialSt

calcularEEsc :: Exp -> Either Errores Exp
calcularEEsc e = ST.evalStateT (travExp e) initialSt

initialStepper :: SEstado
initialStepper = Step 1 [M.empty]

debbugEnv :: Exp -> Either Errores (Exp,SEstado)
debbugEnv e = ST.runStateT (travExp e) initialStepper
