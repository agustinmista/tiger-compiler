{-# LANGUAGE TypeSynonymInstances,FlexibleInstances, TypeFamilies #-}
module TigerSeman where

import TigerAbs
import TigerEnv
import TigerErrores as E
import TigerSres
import TigerTemp
import TigerTips
import TigerTrans

import qualified Data.Map.Strict as M
import qualified Control.Monad.State as ST
import Control.Monad
import Data.Monoid
import Control.Arrow
import Control.Monad.Except
import Control.Conditional as C
import Data.List
import Data.Ord
import Prelude as P hiding (foldl') 

import qualified Data.Graph as G
import qualified Data.Text as T

import Debug.Trace

none :: BExp
none = Ex $ Const 1

ifNM b t f = ifM (not <$> b) t f

-- Helper para debug
debug msg = trace msg (return ())

remDup :: Ord a => [a] -> [a]
remDup = concat . filterByLength (==1)

filterByLength :: Ord a => (Int -> Bool) -> [a] -> [[a]]
filterByLength p = filter (p . length) . group . sort


-- | Clase general que propongo para realizar el análisis semántico.
class (TLGenerator w, NotFounder w) => Manticore w where
    -- | Insertar un valor en el espacio de valores definidos.
    insertValV :: Symbol -> ValEntry -> w ()
    -- | Insertar una función en el espacio de funciones definidas
    insertFunV :: Symbol -> FunEntry -> w ()
    -- | Insertar un valor de solo lectura. De todas maneras, se pide memoria en
    -- el val entry. DEPRECATED
    insertVRO :: Symbol -> ValEntry -> w ()
    insertVRO = insertValV
    -- | Insertar un tipo al espacio de tipos. Ej: 'insertTipoT "Entero" (TInt RW)'
    insertTipoT :: Symbol -> Tipo -> w ()
    -- | Dado el nombre de una función, obtener la información que guardamos en
    -- la definición
    getTipoFunV :: Symbol -> w FunEntry
    -- | Dado el nombre de un valor, obtener la información que guardamos en
    -- la definición
    getTipoValV :: Symbol -> w ValEntry
    -- | Dado el nombre de un tipo, obtener el tipo interno del compilador.
    getTipoT :: Symbol -> w Tipo
    -- | Utilizada para guardar el estado de definiciones, util al momento de
    -- hacer las declaraciones.
    setRPoint :: w ()
    -- | Utilizada para reestablecer el estado de definiciones, util al momento de
    -- hacer las declaraciones.
    restoreRPoint :: w ()

    -- | Retornar errores de tipos con mensajes 
    errorTT :: Pos -> String -> String -> w a
    errorTT p exp msg = E.error $ internal $ T.pack $ "  en la posicion: " ++ printPos p ++ "\n" ++ 
                                                      "  en la expresion:\n" ++ tabbedExp ++ 
                                                      "  error de tipos:\n\t" ++ msg
                                                                where tabbedExp = unlines $ map ("\t"++) $ lines exp
    -- DEBUG --
    -- | Función de Debugging que muestra el entorno de valores
    showVEnv :: w ()
    -- | Función de Debugging que muestra el entorno de tipos
    showTEnv :: w ()
    -- | Debugging entrega 2
    showEnt2 :: w ()
    --

    --  | Tiposiguales, es relativo y necesario por la definición de 'Tipo' que
    --  propuse en TigerTips.hs . Viene gratis...
    tiposIguales :: Tipo -> Tipo -> w Bool 
    tiposIguales (RefRecord s) l@(TRecord _ u) = do
        st <- getTipoT s
        case st of
            TRecord _ u1 -> return (u1 == u)
            ls@(RefRecord s') -> tiposIguales ls l
            _ -> E.error $ internal $ T.pack $ "no son tipos iguales... 123+1"
    tiposIguales l@(TRecord _ u) (RefRecord s) = do
        st <- getTipoT s
        case st of
            TRecord _ u1 -> return (u1 == u)
            ls@(RefRecord s') -> tiposIguales l ls 
            _ -> E.error $ internal $ T.pack $ "no son tipos iguales... 123+2"
    tiposIguales (RefRecord s) (RefRecord s') = do
        s1 <- getTipoT s
        s2 <- getTipoT s'
        tiposIguales s1 s2
    tiposIguales TNil  (RefRecord _) = return True
    tiposIguales (RefRecord _) TNil = return True
    tiposIguales (RefRecord _) _ = E.error $ internal $ T.pack $ "no son tipos iguales... 123+3"
    tiposIguales  e (RefRecord s) = E.error $ internal $ T.pack $ "no son tipos iguales... 123+4" ++ (show e ++ show s)
    tiposIguales a b = return (intiposIguales a b)
    
    -- | Generador de 'Unique' para las definiciones de los tipos records,
    -- array, etc.
    ugen :: w Unique
    --

    -- Funcion para agregar un batch de tipos al entorno, buscando los ciclos.
    -- Utiliza un sort topologico. Primero construye un grafo con las dependencias
    -- y luego llama a la libreria.
    addTypos :: [(Symbol, Ty, Pos)] -> w () 
    addTypos dls = 
        let 
            (rs, ms) = foldl' (\(ds, ms) (s,ss, p) -> ((s,s, depend ss): ds , (s,(ss,p)) : ms)) ([],[]) dls
            (g, f, _) = G.graphFromEdges rs
            dls' = M.fromList ms
            tp = G.topSort g
            symbols = map (\(x,_,_) -> x) dls
        in if length symbols /= length (remDup symbols)
            then let dupTypes = map (show . T.unpack . head) $ filterByLength (>1) symbols
                     listedDups = intercalate "," dupTypes
                 in E.error $ internal $ T.pack $ "declaraciones de tipos " ++ listedDups ++ " repetidas en el batch"
            else do
                mapM_ (\(s,ty,p) -> case ty of
                                RecordTy {} -> insertTipoT s (RefRecord s)
                                _ -> return ()) dls
                mapM_ (\x -> do
                        let (s,_ ,_) = f x
                        let (ty,p) = dls' M.! s
                        t <- handle (transTy ty) (\t -> E.error $  internal $ T.pack $ "se encontraron dependencias ciclicas o hay declaraciones de tipo interrumpidas")
                        insertTipoT s t 
                    )  (reverse tp)
        

-- | COMPLETAR
--
addpos t p exp = handle t  (\e -> E.error $ adder e (T.pack $ "  en la posicion: " ++  printPos p ++ "\n" ++ 
                                                              "  en la expresion:\n" ++ tabbedExp ++
                                                              "  error de tipos:\n\t"))
                                                                   where tabbedExp = unlines $ map ("\t"++) $ lines exp


-- | Un ejemplo de estado que alcanzaría para realizar todas la funciones es:
data EstadoG = G { unique      :: Int
                 , vEnv        :: Stack Lion (Mapper Lion Symbol EnvEntry)
                 , tEnv        :: Stack Lion (Mapper Lion Symbol Tipo)
                 -- Entrega 2
                 , stLevel     :: Stack Lion Level
                 , actualLevel :: Int
                 , utemp       :: Int
                 , ulbl        :: Int
                 , fragStack   :: Stack Lion TransFrag
                 , stSalida    :: Stack Lion (Maybe Label)
                 } deriving Show


-- | Acompañado de un tipo de errores
data SEErrores = NotFound T.Text 
               | DiffVal T.Text 
               | Internal T.Text

instance Show SEErrores where
    show (NotFound t) = T.unpack t
    show (DiffVal t) = T.unpack t
    show (Internal t) = T.unpack t


-- | Podemos definir el estado inicial como:
lionConf :: EstadoG
lionConf = G {unique = 0
            , stLevel = StackL [outermost]
            , stSalida = StackL []
            , actualLevel = 0
            , utemp = 0
            , ulbl = 0
            , fragStack = StackL []
            , tEnv = StackL [Map $ M.insert (T.pack "int") (TInt RW) (M.singleton (T.pack "string") TString)]
            , vEnv = StackL [ Map $ M.fromList
                    [(T.pack "print", Func (outermost,T.pack "print",[TString], TUnit, True))
                    ,(T.pack "flush", Func (outermost,T.pack "flush",[],TUnit, True))
                    ,(T.pack "getchar",Func (outermost,T.pack "getchar",[],TString,True))
                    ,(T.pack "ord",Func (outermost,T.pack "ord",[TString],TInt RW,True)) -- Ojota con este intro...
                    ,(T.pack "chr",Func (outermost,T.pack "chr",[TInt RW],TString,True))
                    ,(T.pack "size",Func (outermost,T.pack "size",[TString],TInt RW,True))
                    ,(T.pack "substring",Func (outermost,T.pack "substring",[TString,TInt RW, TInt RW],TString,True))
                    ,(T.pack "concat",Func (outermost,T.pack "concat",[TString,TString],TString,True))
                    ,(T.pack "not",Func (outermost,T.pack "not",[TInt RW],TInt RW,True))
                    ,(T.pack "exit",Func (outermost,T.pack "exit",[TInt RW],TUnit,True))
                    ]]}


-- | Defino la monada que va a llevar el estado y devolver o un error o alguna otra pavada (por ahora, un tipo)
type Lion = ST.StateT EstadoG (Either SEErrores)

-- | Ahora puedo poner la monada a trabajar
runLion :: Exp -> Either SEErrores ([TransFrag],Int,Int)
runLion e = case ST.runStateT (transExp (LetExp [FunctionDec [(T.pack "_tigermain",[],Just $ T.pack "int",e,Simple 0 0)]] (IntExp 0 (Simple 0 1)) (Simple 0 2))) lionConf of
                Left x -> Left x
                Right ((e,_), est) -> Right (fragToList $ fragStack est,utemp est, ulbl est)

-- | Muestro que todo leon tiene genera labels
instance TLGenerator Lion where
    newTemp  = do
        st <- ST.get
        let l = utemp st
        ST.put(st{utemp = l+1})
        return $ detgenTemp l
    newLabel = do
        st <- ST.get
        let l = ulbl st
        ST.put(st{ulbl = l+1})
        return $ detgenLabel l

-- | Debo mostrar que todo leon puede andar en manada
instance Environmental Lion where
    data Mapper Lion a b = Map (M.Map a b) deriving Show
    emptyI = Map M.empty
    insertI s d (Map e) = Map $ M.insert s d e
    updateI = insertI
    lookupI s (Map e) = M.lookup s e
    intersecI f (Map m1) (Map m2) = Map $ M.intersectionWith f m1 m2

-- Tengo que mostrar que un leon es un daemon
instance Daemon Lion where
    data Error Lion = E SEErrores
    error (E e) = throwError e
    handle m f = catchError m (f . E)
    internal = E . Internal
    adder (E e) e1 = E $ eappend e e1
        where eappend (NotFound t) t1 = NotFound (T.append t1 t)
              eappend (DiffVal t) t1 = DiffVal (T.append t1 t)
              eappend (Internal t) t1 = Internal (T.append t1 t)

-- Tambien debo mostrar que el leon a veces se muere de hambre
instance NotFounder Lion where
    notfound = E . NotFound

-- | COMPLETAR
instance FlorV Lion where
        pushLevel l = do
            st <- ST.get
            nst <- push l (stLevel st)
            ST.put (st{stLevel=nst})
        popLevel = do
            st <- ST.get
            nst <- pop (stLevel st) `addLer` "popLevel"
            ST.put (st{stLevel=nst})
        topLevel = do
            st <- ST.get
            top (stLevel st) `addLer` "topLevel"
        getActualLevel = do
            st <- ST.get
            return $ actualLevel st
        upLvl =  do
            st <- ST.get
            let nl = actualLevel st
            ST.put $ st{actualLevel = nl +1}
        downLvl =  do
            st <- ST.get
            let nl = actualLevel st
            ST.put $ st{actualLevel = nl -1}
        pushFrag f = do
            st <- ST.get
            nf <- push f (fragStack st)
            ST.put $ st{fragStack=nf}
        getFrags = do
            st <- ST.get
            let (StackL xs) = fragStack st
            return xs
        pushSalida l = do
            st <- ST.get
            newst <- push l (stSalida st)
            ST.put (st{stSalida=newst})
        topSalida = do
            st <- ST.get
            top (stSalida st) `addLer` "topSalida"
        popSalida = do
            st <- ST.get
            newst <- pop (stSalida st) `addLer` "popSalida"
            ST.put (st{stSalida=newst})


-- | Tambien hace falta mostrar que Lion puede usar una lista como un stack
instance Stacker Lion where
    data Stack Lion x = StackL [x]
    push x (StackL st) =  return $ StackL (x:st)
    pop (StackL st) = case st of
        (x:xs) -> return $ StackL xs
        _ ->  E.error $ internal $ T.pack "empty stack"
    top (StackL st) = case st of
        (x:_) -> return x
        _ ->  E.error $ internal $ T.pack "empty stack"

instance (Show a) => Show (Stack Lion a) where
    show (StackL x) = "Stack" ++ (foldr (\t ts -> show t ++ '\n':ts) "" x)

-- | Ahora si, puedo ver que si el leon tiene todo lo anterio,
-- entonces puede volar
instance Manticore Lion where
    ugen = do
        st <- ST.get
        let u = unique st
        ST.put (st{unique = u+1})
        return u
    showTEnv = do
        tenv <- getTEnv `addLer` "showTEnv"
        trace (show tenv) (return ())
    showVEnv = do
        venv <- getVEnv `addLer` "showVEnv"
        trace (show venv) (return ())
    insertVRO = insertValV 
    insertValV s ventry = do
        venv <- getVEnv `addLer` "insertValV"
        setVEnv $ insertI s (Var ventry) venv
    getTipoValV s = do
        venv <- getVEnv `addLer` "getTipoValV"
        case lookupI s venv of
            Nothing -> E.error $ notfound (T.append s (T.pack " getTipoValV/Nothing "))
            Just (Var v) -> return v
            _ -> E.error $ internal $ T.pack $ "la variable " ++ show s ++ " no es una funcion" 
    insertFunV s fentry = do
        venv <- getVEnv `addLer` "insertFunV"
        setVEnv $ insertI s (Func fentry) venv
    getTipoFunV s = do
        venv <- getVEnv `addLer` "getTipoFunV"
        case lookupI s venv of
                Nothing -> E.error $ notfound (T.append s (T.pack " getTipoFunV/Nothing "))
                Just (Func f) -> return f
                _ -> E.error $ internal $ T.pack $ "la variable " ++ show s ++ " no es una funcion"
    insertTipoT s t = do
        tenv <- getTEnv `addLer` "insertTipoT"
        setTEnv $ insertI s t tenv
    getTipoT s = do
        tenv <- getTEnv `addLer` "getTipoT"
        case lookupI s tenv of
            Nothing -> E.error $ notfound (T.append s (T.pack " getTipoT/Nothing"))
            Just p -> return p
    setRPoint = do
        venv <- getVEnv `addLer` "setRPoint"
        tenv <- getTEnv `addLer` "setRPoint"
        setVEnv venv
        setTEnv tenv
    restoreRPoint = do
        st <- ST.get
        vs <- pop (vEnv st) `addLer` "restoreRPoint"
        ts <- pop (tEnv st) `addLer` "restoreRPoint"
        ST.put (st{vEnv = vs, tEnv = ts})
    showEnt2 = do
        st <- ST.get
        let traceLev = "\nstLevel:" ++ (show $ stLevel st)
        let traceSal = "\nstSalida:" ++ (show $ stSalida st)
        let aclvl = "\nActualLevel:" ++ (show $ actualLevel st)
        let tmp = "\nTempGen:" ++ (show $ utemp st)
        let lbl = "\nLabelGen:" ++ (show $ ulbl st)
        let frStack ="\nFragStack:" ++ (show $ fragStack st)
        ST.put (trace (traceLev ++ traceSal ++ aclvl ++ tmp ++ lbl ++ frStack) st)

-- | Auxiliares para la instancia de Manticore Lion
getVEnv :: Lion (Mapper Lion Symbol EnvEntry)
getVEnv = do
    st <- ST.get
    addLer (top (vEnv st)) "getVEnv"

getTEnv :: Lion (Mapper Lion Symbol Tipo)
getTEnv = do
    st <- ST.get
    addLer (top (tEnv st)) "getTEnv"

setVEnv :: Mapper Lion Symbol EnvEntry -> Lion ()
setVEnv venv = do
    st <- ST.get
    venv' <- push venv (vEnv st)
    ST.put (st{vEnv = venv'})

setTEnv :: Mapper Lion Symbol Tipo -> Lion ()
setTEnv tenv = do
    st <- ST.get
    tenv' <- push tenv (tEnv st)
    ST.put (st{tEnv = tenv'})

depend :: Ty -> [Symbol]
depend (NameTy s) = [s]
depend (ArrayTy s) = [s]
depend (RecordTy ts) = concatMap (\(_,_,t) -> depend t) ts

fragToList :: Stack Lion a -> [a]
fragToList (StackL xs) = xs


genLabel s p@(Simple l c) u = return $ s <> T.pack ("." ++ show l ++ "." ++ show c ++ "." ++ show u)  
genLabel s p u = E.error $ internal $ T.pack $ "error generando el label para " ++ show s ++ " en " ++ printPos p  

okOp :: Tipo -> Tipo -> Oper -> Bool
okOp TNil TNil EqOp = False
okOp TUnit _ EqOp = False
okOp _ _ EqOp = True
okOp TNil TNil NeqOp = False
okOp TUnit _ NeqOp = False
okOp _ _ NeqOp = True

cmpZip :: (Manticore m) =>  [(Symbol, Tipo)] -> [(Symbol, Tipo, Int)] -> m (M.Map Symbol Int,Bool)
cmpZip [] [] = return (M.empty,True)
cmpZip [] _ = return (M.empty, False)
cmpZip _ [] = return (M.empty,False)
cmpZip ((sl,tl):xs) ((sr,tr,p):ys) = do
        b <- tiposIguales tl tr
        if b  && (sl == sr) then
                    do
                        (m,b) <- cmpZip xs ys
                        let nm = M.insert sl p m
                        return (nm,b)
                else return (M.empty,False)

buscarM :: Symbol -> [(Symbol, Tipo, Int)] -> Maybe (Int,Tipo)
buscarM s [] = Nothing
buscarM s ((s',t,i):xs) | s == s' = Just (i,t)
                        | otherwise = buscarM s xs


--------------------------------------------------------------------------------
transVar :: (Manticore w, FlorV w) => Var -> w (BExp, Tipo)
transVar (SimpleVar s) = do
    (ty, acc, lvl) <-  getTipoValV s
    be <- simpleVar acc lvl
    return (be, ty)
transVar (FieldVar v s) = do 
        (cv, tv) <- transVar v
        case tv of
            TRecord xs _ -> case buscarM s xs of
                Just (pos,t) -> do
                    be <- fieldVar cv pos
                    return (be,t)
                _ -> E.error $ internal $ T.pack $ "record: el campo " ++ T.unpack s ++" no está definido"
            RefRecord t -> do 
                TRecord xs _  <- getTipoT t
                case buscarM s xs of
                    Just (pos, t) -> do
                        be <- fieldVar cv pos
                        return (be, t) 
                    _ -> E.error $ internal $ T.pack $ "record: el campo " ++ T.unpack s ++" no está definido"
            x -> E.error $ internal $ T.pack $ "record: la variable no tiene tipo record sino " ++ show x 
transVar (SubscriptVar v e) = do
        (ce, te) <- transExp e
        C.unlessM (tiposIguales te $ TInt RW) $ E.error $ internal $ T.pack $ "array: el indice no es un entero"
        (cv, tv) <- transVar v
        case tv of 
            TArray t _ -> do
                cod <- subscriptVar cv ce                
                return (cod, t)
            x -> E.error $ internal $ T.pack $ "array: la variable no tiene tipo array sino " ++ show x 

transTy :: (Manticore w) => Ty -> w Tipo
transTy (NameTy s) = getTipoT s
transTy (ArrayTy s) = do
        u <- ugen
        t <- getTipoT s
        return $ TArray t u 
transTy (RecordTy flds) = do 
        let sortedFlds = sortBy (comparing (\(s,_,_)->s)) flds
            zippedFlds = zip sortedFlds [1..]  -- (fld, n)
        typedFlds <- mapM (\((s, _, t),n) -> do
                            t' <- transTy t
                            return (s, t', n)) zippedFlds
        u <- ugen
        return $ TRecord typedFlds u

fromTy :: (Manticore w) => Ty -> w Tipo
fromTy (NameTy s) = getTipoT s
fromTy _ = P.error "no debería haber una definición de tipos en los args..."


transDec :: (Manticore w, FlorV w) => Dec -> w [BExp] -- por ahora...
transDec w@(TypeDec ls) = let (_,_,p) = head ls
                          in do addpos (addTypos ls) p (ppD w)
                                return []
transDec w@(VarDec s mb mty init p) = do
        (cinit, ety) <- transExp init
        case mty of
            Just ty -> do
                    tty <- addpos (getTipoT ty) p
                    ifNM (tiposIguales tty ety) (errorTT p (ppD w) $ "Se esperaba un valor de tipo " ++ show ty ++ " y se tiene un valor de tipo " ++ show ety) $ return ()
            Nothing -> return ()
        nlvl <- getActualLevel
        acc <- allocLocal (isJust mb)
        insertValV s (ety,acc, nlvl)
        return [cinit]
transDec w@(FunctionDec fb) = do
        mapM_ (\(nm, args, mret, bd, p) -> do
            u <- ugen
            let lbl = T.append nm $ T.append (T.pack $ '.' : posToLabel p) (T.pack $ '.' : show u)
            (tps,escs) <- foldM (\(tys,escs) (_,esc,t) -> do
                    ty <- fromTy t
                    case esc of
                        Just True -> return (ty:tys, True :escs)
                        _ -> return (ty:tys, False :escs)
                    ) ([],[]) args
            level <- topLevel -- level actual
            let nlvl = newLevel level lbl (reverse escs)
            case mret of
                Just p' -> do
                    ty <- getTipoT p'
                    insertFunV nm (nlvl,lbl,reverse tps,ty,False)
                Nothing -> insertFunV nm (nlvl,lbl,tps,TUnit,False)
            ) fb -- insertamos todos las interfaces de las funciones...
        mapM (\(nm, args, mret, bd, p) -> do
            (nlvl,lbl,argsty,ty,_) <- getTipoFunV nm
            preFunctionDec nlvl
            setRPoint -- guardamos el entorno
            actualLev <- getActualLevel
            mapM_ (\((nm,b,_), typ) -> do
                acc <- allocArg (isJust b)
                insertValV nm (typ,acc,actualLev)) (zip args argsty)
            t <- topLevel
            (cb, tyb) <- transExp bd
            ifNM (tiposIguales ty tyb) (errorTT p (ppD w)  $ "El cuerpo de la función " ++ show nm ++ " tiene tipo " ++ show tyb ++ " y se esperaba " ++ show ty)
             $ do
                e <- ifM (tiposIguales tyb TUnit) (functionDec cb t True) (functionDec cb t False)
                restoreRPoint
                posFunctionDec
                return e
                    ) fb
     
transExp :: (Manticore w, FlorV w) => Exp -> w (BExp, Tipo)
transExp w@(VarExp v p) = addpos (transVar v) p (ppE w) 
transExp (UnitExp {}) = do
    c <- unitExp
    return (c,TUnit)
transExp (NilExp {}) = do
    c <- nilExp
    return (c,TNil)
transExp (IntExp i _) = do
    c <- intExp i
    return (c,TInt RW)
transExp (StringExp s _) = do
    c <- stringExp $ T.pack s
    return (c,TString)
transExp w@(CallExp nm args p) = do 
        (lvl, lbl, as, ret, ext) <- addpos (getTipoFunV nm) p
        args' <- zipWithM (\ earg rarg -> do
                                (carg, tearg) <- transExp earg
                                ifNM (tiposIguales tearg rarg) (errorTT p $ "CallExp:Tipos diferentes" ++ show tearg ++ show rarg)
                                 $ return carg) args as
        -- Eventualmente querriamos obtener los IR de cada exp..
        c <- ifM (tiposIguales ret TUnit)
                (callExp lbl ext True  lvl args')
                (callExp lbl ext False lvl args')
        return (c,ret)
transExp w@(OpExp el' oper er' p) = do -- Esta va gratis
        (cl,el) <- transExp el'
        (cr,er) <- transExp er'
        ifNM (tiposIguales el er) (errorTT p (ppE w) ("OpExp:Tipos diferentes" ++ show el ++ show er))
         $  case oper of
                EqOp  ->
                        if (okOp el er oper)
                        then do
                                c <- ifM (tiposIguales el TString) (binOpStrExp cl oper cr) (binOpIntRelExp cl oper cr)
                                return (c,TInt RW)
                        else (errorTT p (ppE w) ("Tipos no comparables " ++ show el ++ show er ++ show oper))
                NeqOp ->
                        if (okOp el er oper)
                        then do
                                c <- ifM (tiposIguales el TString) (binOpStrExp cl oper cr) (binOpIntRelExp cl oper cr)
                                return (c,TInt RW)
                        else (errorTT p (ppE w) ("Tipos no comparables " ++ show el ++ show er ++ show oper))
                PlusOp ->
                        ifNM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("Tipo " ++ show el' ++ " no es un entero"))
                        $ binOpIntExp cl oper cr >>= \c -> return (c,TInt RW)
                MinusOp ->
                         ifNM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("Tipo " ++ show el' ++ " no es un entero"))
                         $ binOpIntExp cl oper cr >>= \c -> return (c,TInt RW)
                TimesOp -> ifNM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("Tipo " ++ show el' ++ " no es un entero"))
                            $ binOpIntExp cl oper cr >>= \c -> return (c,TInt RW)
                DivideOp ->
                        ifNM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("Tipo " ++ show el' ++ " no es un entero"))
                        $ binOpIntExp cl oper cr >>= \c -> return (c,TInt RW)
                _ -> ifM (tiposIguales el $ TInt RW)
                                (do
                                    c <- binOpIntRelExp cl oper cr
                                    return (c, TInt RW))
                                (ifM (tiposIguales el TString)
                                    (do
                                        c <- binOpStrExp cl oper cr
                                        return (c, TInt RW))
                                    (errorTT p (ppE w) ("Elementos de tipo" ++ show el ++ "no son comparables")))

transExp w@(RecordExp flds rt p) = do  -- Se debe respetar el orden de los efectos
        recTy <- addpos (getTipoT rt) p -- Buscamos el tipo de rt
        case recTy of -- Chequeamos que el tipo real sea Record...
            TRecord rflds _ -> do
                flds'' <- mapM (\(s,e) -> do {(ce,e') <- transExp e; return ((ce,s),(s,e'))}) flds
                let (cds,flds') = unzip flds''
                let sflds = List.sortBy (comparing fst) flds' -- Asumimos que estan ordenados los campos del record.
                (m, b) <- cmpZip flds' rflds
                if b
                    then do
                        c <- recordExp (map (\(cb,s) -> (cb,m M.! s)) cds)
                        return (c, recTy)
                    else (errorTT p (ppE w) $ "Error en los campos del records..." ++ show flds' ++ show rflds)
            _ -> errorTT p (ppE w) ("El tipo[" ++ show rt ++ "NO es un record")

transExp (SeqExp es p) = do -- Va gratis
        es' <- mapM transExp es
        let ess = map fst es'
        let (_,ty) = last es'
        c <- seqExp ess
        return (c,ty)

transExp w@(AssignExp var exp p) = do
        (cv,tvar) <- transVar var
        (cvl,tval) <- transExp val
        ifM (not <$> (tiposIguales tvar tval)) (errorTT p (ppE w) "Error diferentes tipos en la asignación")
            (if tvar == (TInt RO)
                then (errorTT p (ppE w) $ "La variable " ++ show var ++ " es de tipo read only")
                else (assignExp cv cvl >>= \c ->return (c,TUnit)))

transExp w@(IfExp co th Nothing p) = do
        (cco,co') <- transExp co
        ifM (not <$> tiposIguales co' (TInt RW)) (errorTT p "Error en la condición")
            $ transExp th >>= \(cth,th') ->
                ifM (not <$> tiposIguales th' TUnit) (errorTT p "La expresión del then no es de tipo unit")
                 $ ifThenExp cco cth >>= \c -> return (c,TUnit)

transExp w@(IfExp co th (Just el) p) = do 
        (cco,co') <- transExp co
        ifNM (tiposIguales co' $ TInt RW) (errorTT p (ppE w) "Error en la condición")
            $   do
                    (cth,th') <- transExp th
                    (cel,el') <- transExp el
                    ifNM (tiposIguales th' el') (errorTT p (ppE w) "Los branches tienen diferentes tipos...")
                        $ ifThenElseExp cco cth cel >>= \c -> return (c,th')

transExp w@(WhileExp co body p) = do
        (cco,co') <- transExp co
        ifNM (tiposIguales co' $ TInt RW) (errorTT p (ppE w) "La condición no es un booleano")
            $
            preWhileforExp >>
            transExp body >>= \(cb,body') ->
            ifNM (tiposIguales body' TUnit) (errorTT p (ppE w) "El body del while no es de tipo unit...")
            $ do
                lvl <- topLevel
                c <- whileExp cco cb
                posWhileforExp
                return (c,TUnit)

transExp w@(ForExp nv mb lo hi bo p) = do
        (clo,lo') <- transExp lo
        ifNM (tiposIguales lo' $ TInt RW) (errorTT p (ppE w) "La cota inferior no es un int...")
            $ transExp hi >>= \(chi,hi')  ->
            ifNM (tiposIguales hi' $ TInt RW) (errorTT p (ppE w) "La cota superior no es un int...")
            $ do
                setRPoint -- guardamos antes de insertar el iterador
                --- Generamos eliterador
                preWhileforExp
                nlvl <- getActualLevel
                acc <- allocLocal (isJust mb)
                insertVRO nv (TInt RO, acc, nlvl)
                cvar <- varDec acc
                ---
                (cbo,bo') <- transExp bo
                ifNM (tiposIguales bo' TUnit) (errorTT p (ppE w) "el cuerpo del for tiene que ser de tipo unit...")
                 $ do
                    c <- forExp clo chi cvar cbo
                    posWhileforExp
                    restoreRPoint -- volvemos al punto anterior
                    return (c,TUnit)

transExp(LetExp dcs body p) = do -- Va gratis...
        setRPoint
        dcs' <- mapM transDec dcs
        let dcs'' = concat dcs'
        (cb,b) <- transExp body
        c <- letExp dcs'' cb
        restoreRPoint
        return (c,b)

transExp(BreakExp p) = do
    c <- breakExp
    return (c,TUnit)

transExp w@(ArrayExp sn cant init p) = do
        ty <- getTipoT sn
        case ty of
            TArray t _ -> do
                (ccant,cant') <- transExp cant
                ifNM (tiposIguales cant' $ TInt RW) (errorTT p  (ppE w) "La cantidad debería ser int...")
                 $ transExp init >>= \(cinit,tinit) ->
                    ifNM (tiposIguales tinit t) (errorTT p (ppE w) $ "el valor inicial es de tipo " ++ show tinit ++ " cuando debería ser " ++ show t)
                        $ arrayExp ccant cinit >>= \c -> return (c,ty)
            _ -> errorTT p (ppE w) $ "Se esperaba un elemento de tipo " ++ show ty
