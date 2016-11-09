{-# LANGUAGE TypeSynonymInstances,FlexibleInstances, TypeFamilies #-}
module TigerSeman where

import TigerAbs
import TigerEnv
import TigerErrores as E
import TigerSres
import TigerTemp
import TigerTips
import TigerTrans
import TigerPretty

--import qualified TigerTree as Tree (Exp) 
import TigerTree hiding (Exp)

import qualified Data.Map.Strict as M
import qualified Control.Monad.State as ST
import Control.Monad
import Control.Applicative hiding (Const)
import Data.Either
import Data.Maybe
import Data.Bifunctor
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
debug msg = trace (show msg) (return ())

remDup :: Ord a => [a] -> [a]
remDup = concat . filterByLength (==1)

filterByLength :: Ord a => (Int -> Bool) -> [a] -> [[a]]
filterByLength p = filter (p . length) . group . sort


-- | Clase general que propongo para realizar el análisis semántico.
class (Functor w, TLGenerator w, NotFounder w) => Manticore w where
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
runLion :: Exp -> Either SEErrores ([TransFrag], Int, Int)
runLion e = bimap id unpackFrags $ ST.runStateT (linkMain e) lionConf 
                where unpackFrags (_, est) = (fragToList $ fragStack est, utemp est, ulbl est) 
                      linkMain e = transExp (LetExp [FunctionDec [(T.pack "_tigermain",[],Just $ T.pack "int", e, Simple 0 0)]]
                                                (IntExp 0 (Simple 0 1)) (Simple 0 2))

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




transDec w@(VarDec s mb Nothing init p) = do
       (cinit, tinit)     <- transExp init
       nlvl               <- getActualLevel
       acc                <- allocLocal (isJust mb) 
       case tinit of 
                TNil    -> errorTT p (ppD w) "declaracion: se intento asignar Nil a una variable sin signatura de tipo"
                TInt RO -> insertValV s (TInt RW,acc,nlvl)
                t       -> insertValV s (t, acc, nlvl)
       vdexp <- varDec acc 
       vd <- assignExp vdexp cinit
       return [vd]
        

transDec w@(VarDec s mb (Just t) init p) = do
       (cinit, tinit) <- transExp init
       t' <- addpos (getTipoT t) p (ppD w)
       C.unlessM (tiposIguales t' tinit) (errorTT p (ppD w) $ "Se esperaba un valor de tipo " ++ show t' ++ " y se tiene un valor de tipo " ++ show tinit)
       nlvl <- getActualLevel
       acc <- allocLocal (isJust mb)
       insertValV s (t',acc, nlvl)
       vdexp <- varDec acc 
       vd <- assignExp vdexp cinit
       return [vd]
        
        



transDec w@(FunctionDec fb) =
    let symbols = map (\(s,_,_,_,_) -> s) fb --extraemos los nombres
        (_,_,_,_,p) = head fb                --la posicion de la 1ra 
    in if length symbols /= length (remDup symbols)  --chequeamos que no haya funciones declaradas dos veces en el mismo batch
        then let dupFuncs =  map (show . T.unpack . head) $ filterByLength (>1) symbols
                 listedDups = intercalate "," dupFuncs   
             in errorTT p (ppD w) $ "identificadores de funcion " ++ listedDups ++ " repetidos en un mismo batch"
        else do 
            -- primera pasada insertando las interfaces a la tabla de funciones
            mapM_ (\(s, flds, ms, e, p) -> do
                u <- ugen
                label <- genLabel s p u
                -- obtenemos el tipo y los escapes de cada argumento
                -- acumulamos los efectos de los parametros de derecha a izquierda
                (flds',escs) <- foldM (\(ts, es) (_,esc,t) -> do    
                    ty <- fromTy t                                 
                    case esc of                                      
                        Just True -> do
                            return (ty:ts, True:es)
                        _ -> return (ty:ts, False:es)
                        ) ([],[]) (reverse flds)
                --obtenemos el level actual 
                level <- topLevel 
                --creamos un nuevo level
                let nlvl = newLevel level label escs 
                --analizamos si es un procedimiento o funcion
                --y agregamos la interfaz a la tabla
                case ms of
                    Nothing -> insertFunV s  (nlvl, label, flds', TUnit, False)      
                    Just rt -> do
                        rt' <- getTipoT rt
                        insertFunV s (nlvl, label, flds', rt', False) 
                ) fb  
            -- segunda pasada, insertamos en la tabla de valores los argumentos
            -- y analizamos los cuerpos de las funciones
            mapM (\(s, flds, ms, e, p) -> do
               (nlvl,label,ts,tr,_) <- getTipoFunV s 
               preFunctionDec nlvl
               setRPoint 
               actualLev <- getActualLevel
               -- Insertamos los argumentos a la tabla de valores
               mapM_ (\((s,vesc,_),t) -> do
                        a <- allocArg (isJust vesc)
                        insertValV s (t,a,actualLev)
                     ) (zip flds ts)
               t <- topLevel
               (ce,e') <- transExp e
               C.unlessM (tiposIguales e' tr) (errorTT p (ppD w) $ "se esperaba que el tipo del cuerpo de la funcion " ++
                                                                    show s ++ " fuera " ++ show tr ++ " y se tiene " ++ show e')
               
               ans <- ifM (tiposIguales e'  TUnit) (functionDec ce t True) (functionDec ce t False)
               restoreRPoint
               posFunctionDec
               return ans 
               ) fb


      
transExp :: (Manticore w, FlorV w, Functor w) => Exp -> w (BExp, Tipo)
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
        (lvl,lbl,ts,tr,e) <- handle (getTipoFunV nm) (\t -> errorTT p (ppE w) $ "no se encontro la definicion de la funcion " ++ show nm)
        C.unless (P.length ts == P.length args) $ errorTT p (ppE w) $ "llamada a funcion " ++ T.unpack nm ++ ": numero de argumentos erroneo"

        let checkTypes t e = do -- armo una función que compara un tipo esperado con el
            (c,t') <- transExp e    -- calculado recursivamente, sale con error si falla y retorna los ci
            ifM (tiposIguales t t') (return t)
                (errorTT p (ppE w) $ "llamada a funcion " ++ T.unpack nm ++ ": tipo de argumento invalido, se esperaba "
                           ++ show t ++ " pero se encontro " ++ show t')
            return c
        -- ts:   parametros formales
        -- args: lista de parametros reales (expresiones)
        cs <- zipWithM checkTypes ts args
        c  <- ifM (tiposIguales tr TUnit) 
                  (callExp lbl e True  lvl cs)
                  (callExp lbl e False lvl cs)
        return (c,tr)

transExp w@(OpExp el' oper er' p) = do -- Esta va gratis
        (cl,el) <- transExp el'
        (cr,er) <- transExp er'
        C.unlessM (tiposIguales el er) (errorTT p (ppE w) ("tipos " ++ show el ++ " y " ++ show er ++ " no son comparables"))
        case oper of
            EqOp  -> do
                    C.unless (okOp el er oper) (errorTT p (ppE w) ("tipos " ++ show el ++ " y " ++ show er ++ " no son comparables mediante " ++ show oper))
                    c <- ifM (tiposIguales el TString) (binOpStrExp cl oper cr) (binOpIntRelExp cl oper cr)
                    return (c,TInt RW)                  
            NeqOp -> do
                    C.unless (okOp el er oper) (errorTT p (ppE w) ("tipos " ++ show el ++ " y " ++ show er ++ " no son comparables mediante " ++ show oper))
                    c <- ifM (tiposIguales el TString) (binOpStrExp cl oper cr) (binOpIntRelExp cl oper cr)
                    return (c,TInt RW)
            PlusOp -> do
                    C.unlessM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("tipos " ++ show el' ++ " no es un entero"))
                    binOpIntExp cl oper cr >>= \c -> return (c,TInt RW)
  
            MinusOp ->do
                     C.unlessM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("tipos " ++ show el' ++ " no es un entero"))
                     binOpIntExp cl oper cr >>= \c -> return (c,TInt RW)
            TimesOp -> do
                        C.unlessM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("tipos " ++ show el' ++ " no es un entero"))
                        binOpIntExp cl oper cr >>= \c -> return (c,TInt RW)
            DivideOp -> do  
                    C.unlessM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("tipos " ++ show el' ++ " no es un entero"))
                    binOpIntExp cl oper cr >>= \c -> return (c,TInt RW) 
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
        rType <- addpos (getTipoT rt) p (ppE w) -- Buscamos el tipo de rt
        case rType of 
            TRecord decFlds _ -> do
                typedFlds <- mapM (\(s,e) -> transExp e >>= \(ce,e') -> return ((ce,s),(s,e')) ) flds                
                let (cs,flds') = unzip typedFlds
                    sortedFlds = sortBy (comparing fst) flds'
                (mon,cond) <- cmpZip sortedFlds decFlds 
                if cond
                    then ( ( recordExp (map (\(cb,s) -> (cb,mon M.! s)) cs)) >>= \c -> return (c,rType) )
                    else (errorTT p (ppE w) $ "record invalido, se esperaba: " ++ show decFlds
                                                    ++ " pero se encontro: " ++ show typedFlds)
            _ -> errorTT p (ppE w) $ "se esperaba un record, pero se encontro: " ++ show rt

transExp (SeqExp es p) = do -- Va gratis
        es' <- mapM transExp es
        let ess = map fst es'
        let (_,ty) = last es'
        c <- seqExp ess
        return (c,ty)

transExp w@(AssignExp var exp p) = do
        (cv,var')  <- addpos  (transVar var) p (ppE w)
        (cvl,exp') <- transExp exp
        matches <- tiposIguales var' exp'
        if not matches
           then errorTT p (ppE w) $ "asignacion: se esperaba valor de tipo " ++ show var' ++ " y se tiene valor de tipo " ++ show exp'
           else if var' == (TInt RO)
                then errorTT p (ppE w) "asignacion: se intento asignar una variable RO"
                else (assignExp cv cvl >>= \c ->return (c,TUnit))

transExp w@(IfExp co th Nothing p) = do
        (cco,co') <- transExp co
        C.unlessM (tiposIguales co' $ TInt RW) $ errorTT p (ppE w) $ "if: la condicion no es de tipo " ++ show (TInt RW)
        (cth,th') <- transExp th
        C.unlessM (tiposIguales th' TUnit) $ errorTT p (ppE w) $ "if: el cuerpo no es de tipo " ++ show TUnit
        c <-  ifThenExp cco cth
        return (c,TUnit) 

transExp w@(IfExp co th (Just el) p) = do 
        (cco,co') <- transExp co
        C.unlessM (tiposIguales co' $ TInt RW) $ errorTT p (ppE w) $ "if: la condicion no es de tipo " ++ show (TInt RW)
        (cth,th') <- transExp th
        (cel,el') <- transExp el
        C.unlessM (tiposIguales th' el') $ errorTT p (ppE w) "if: las ramas tienen distinto tipo"
        c <- ifThenElseExp cco cth cel
        return (c,th')


--------------------------------------------------------------------------------




transExp w@(WhileExp co body p) = do
        (cco,co') <- transExp co
        C.unlessM (tiposIguales co' $ TInt RW) $ errorTT p (ppE w) $ "while: la condicion no es de tipo " ++ show (TInt RW)
        preWhileforExp
        (cb,body') <- transExp body
        C.unlessM (tiposIguales body' TUnit) $ errorTT p (ppE w) $ "while: el cuerpo no es de tipo " ++ show TUnit
        lvl <- topLevel
        c <- whileExp cco cb
        posWhileforExp
        return (c,TUnit)

transExp w@(ForExp nv mb lo hi bo p) = do
        (clo,lo') <- transExp lo
        C.unlessM (tiposIguales lo' $ TInt RW) $ errorTT p (ppE w) $ "for: la cota inferior no es de tipo " ++ show (TInt RW)
        (chi,hi') <- transExp hi
        C.unlessM (tiposIguales hi' $ TInt RW) $ errorTT p (ppE w) $ "for: la cota superior no es de tipo " ++ show (TInt RW)
        setRPoint
        preWhileforExp
        nvlv <- getActualLevel
        acc <- allocLocal (isJust mb) 
        insertVRO nv (TInt RO,acc,nvlv)
        cvar <- varDec acc
        (cbo,bo') <- transExp bo
        C.unlessM (tiposIguales bo' $ TUnit) $ errorTT p (ppE w) $ "for: el cuerpo no es de tipo " ++ show TUnit
        c <- forExp clo chi cvar cbo
        posWhileforExp
        restoreRPoint
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
        sn' <- getTipoT sn
        (ccant,cant') <- transExp cant
        (cinit,init') <- transExp init 
        C.unlessM (tiposIguales cant' (TInt RW)) $ errorTT p (ppE w) $ "array: el tamaño no es de tipo " ++ show (TInt RW) 
        case sn' of
            TArray t _ -> do 
                     C.unlessM (tiposIguales t init') $ errorTT p (ppE w) $ "array: se declaro de tipo " ++ show t ++ " y se lo intento inicializar con tipo " ++ show init'
                     c <- arrayExp ccant cinit
                     return (c,sn')
            x -> errorTT p (ppE w) $ "array: el tipo " ++ show x ++  " no es un array"


