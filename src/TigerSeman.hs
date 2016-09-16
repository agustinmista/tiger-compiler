{-# LANGUAGE TypeSynonymInstances,FlexibleInstances, TypeFamilies #-}
module TigerSeman where

import TigerSres
import TigerTips
import TigerEnv
import TigerErrores as E
import TigerAbs
import TigerTemp
import TigerPretty

import qualified Data.Map.Strict as M
import qualified Control.Monad.State as ST
import Control.Monad
import Data.Monoid
import Control.Arrow
import Control.Monad.Except
import Control.Conditional as C
import Data.List as List
import Data.Ord
import Prelude as P 

import qualified Data.Graph as G
import qualified Data.Text as T

import Debug.Trace

-- Helper para debug
debug msg = trace msg (return ())

class (Environmental w, NotFounder w) => Manticore w where
-- Que compartan el espacio de nombres es decisión de la instancia.
    -- Insertar un valor en el espacio de valores definido
    insertValV :: Symbol -> ValEntry -> w ()
    -- Insertar una funcion en el espacio de funciones definidas.
    insertFunV :: Symbol -> FunEntry -> w ()
    -- Insertar un valor de solo lectura.
    insertVRO :: Symbol -> ValEntry -> w  ()
    -- Insertar un tipo al espacio de tipos.
    insertTipoT :: Symbol -> Tipo -> w ()
    -- Dado el nombre de un valor, obtener la informacion que
    -- guardamos en la definicion
    getTipoFunV :: Symbol -> w FunEntry 
    -- Dado el nombre de un valor, obtener la informacion que
    -- guardamos en la definicion
    getTipoValV :: Symbol -> w ValEntry
    -- Dado el nombre de un tipo, obtener el tipo interno del compilador
    getTipoT :: Symbol -> w Tipo
 
    -- Guardar el estado de las definiciones, util al hacer declaraciones
    setRPoint :: w ()
    -- Reestablecer el estado de las definiciones, util al momento de
    -- hacer las declaraciones
    restoreRPoint :: w ()
    --

    -- Retornar errores de tipos con mensajes 
    errorTT :: Pos -> String -> String -> w a
    errorTT p exp msg = E.error $ internal $ T.pack $ "  en la posicion: " ++ printPos p ++ "\n" ++ 
                                                      "  en la expresion:\n\t" ++ exp ++ "\n" ++ 
                                                      "  error de tipos:\n\t" ++ msg
    
    -- DEBUG --
    -- Mostrar el entorno de valores
    showVEnv :: w ()
    -- Mostrar el entorno de los tipos
    showTEnv :: w ()
    --

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
    
    -- Generador de identificadores unicos
    ugen :: w Unique
    --

    -- Funcion para agregar un batch de tipos al entorno, buscando los ciclos.
    -- Utiliza un sort topologico. Primero construye un grafo con las dependencias
    -- y luego llama a la libreria.
    addTypos :: [(Symbol, Ty, Pos)] -> w () 
    addTypos dls = 
        let 
            (rs, ms) = List.foldl' (\(ds, ms) (s,ss, p) -> ((s,s, depend ss): ds , (s,(ss,p)) : ms)) ([],[]) dls
            (g, f, _) = G.graphFromEdges rs
            dls' = M.fromList ms
            tp = G.topSort g
        in do
        mapM_ (\(s,ty,p) -> case ty of
                        RecordTy {} -> insertTipoT s (RefRecord s)
                        _ -> return ()) dls
        mapM_ (\x -> do
                let (s,_ ,_) = f x
                let (ty,p) = dls' M.! s 
                t <- handle (transTy ty) (\t -> E.error $ adder t $ T.append s $ T.pack " -- CICLO DETECTADO!") -- Mejorar el error?
                insertTipoT s t 
            ) tp

addpos t p vexp = handle t  (\t -> E.error $ adder t (T.pack $ "  en la posicion: " ++  printPos p ++ "\n" ++ 
                                                               "  en la expresion: \n\t" ++ ppE vexp ++ "\n" ++
                                                               "  error de tipos: \n\t"))

--addpos t p vexp = handle t  $ \msg -> E.error $ internal $ T.pack $ "  en la posicion: " ++ printPos p ++ "\n" ++ 
--                                                                    "  error de tipos:\n\t" ++ show msg ++ "\n" ++
--                                                                    "  en la expresion:\n\t" ++ ppE vexp
--    


-- Un ejemplo de estado que alcanzaría para realizar todas la funciones es:
data EstadoG = G { unique :: Int
                 , vEnv   :: Stack Lion (Mapper Lion Symbol EnvEntry)
                 , tEnv   :: Stack Lion (Mapper Lion Symbol Tipo)
                 } deriving Show

-- Acompañado de un tipo de errores
data SEErrores = NotFound T.Text 
               | DiffVal T.Text 
               | Internal T.Text

instance Show SEErrores where
    show (NotFound t) = T.unpack t
    show (DiffVal t) = T.unpack t
    show (Internal t) = T.unpack t

--  Podemos definir el estado inicial como:
initConf :: EstadoG
initConf = G { unique = 0
             , tEnv = StackL [ Map $ M.insert (T.pack "int") (TInt RW) (M.singleton (T.pack "string") TString)]
             , vEnv = StackL [ Map $ M.fromList
                     [(T.pack "print", Func (1,T.pack "print",[TString], TUnit, True))
                     ,(T.pack "flush", Func (1,T.pack "flush",[],TUnit, True))
                     ,(T.pack "getchar",Func (1,T.pack "getchar",[],TString,True))
                     ,(T.pack "ord",Func (1,T.pack "ord",[TString],TInt RW,True)) -- Ojota con este intro...
                     ,(T.pack "chr",Func (1,T.pack "chr",[TInt RW],TString,True))
                     ,(T.pack "size",Func (1,T.pack "size",[TString],TInt RW,True))
                     ,(T.pack "substring",Func (1,T.pack "substring",[TString,TInt RW, TInt RW],TString,True))
                     ,(T.pack "concat",Func (1,T.pack "concat",[TString,TString],TString,True))
                     ,(T.pack "not",Func (1,T.pack "not",[TInt RW],TInt RW,True))
                     ,(T.pack "exit",Func (1,T.pack "exit",[TInt RW],TUnit,True))
                     ]]}


-- Defino la monada que va a llevar el estado y devolver o un error o alguna otra pavada (por ahora, un tipo)
type Lion = ST.StateT EstadoG (Either SEErrores)

-- Ahora puedo poner la monada a trabajar
runLion :: Exp -> Either SEErrores Tipo 
runLion e = either Left (Right . fst) $ ST.runStateT (transExp e) initConf

-- Debo mostrar que todo leon puede andar en manada
instance Environmental Lion where
    data Mapper Lion a b = Map (M.Map a b) deriving Show
    emptyI = Map M.empty
    insertI s d (Map e) = Map $ M.insert s d e
    updateI = insertI
    lookupI s (Map e) = M.lookup s e
    intersecI f (Map m1) (Map m2) = Map $ M.intersectionWith f m1 m2

-- Tengo que mostrar que un leon es un deamon (sea lo que eso fuera)
instance Deamon Lion where
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
    notfound = E.notfound

-- Tambien hace falta mostrar que Lion puede usar una lista como un stack
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

-- Ahora si, puedo ver que si el leon tiene todo lo anterio,
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

-- Auxiliares para la instancia de Manticore Lion
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

genLabel s p@(Simple l c) u = return $ s <> T.pack ("." ++ show l ++ "." ++ show c ++ "." ++ show u)  
genLabel s p u = E.error $ internal $ T.pack $ "error generando el label para " ++ show s ++ " en " ++ printPos p  

okOp :: Tipo -> Tipo -> Oper -> Bool
okOp TNil TNil EqOp = True -- PREGUNTAR!
okOp TUnit _ EqOp = False
okOp _ _ EqOp = True
okOp TNil TNil NeqOp = True -- PREGUNTAR!
okOp TUnit _ NeqOp = False
okOp _ _ NeqOp = True

cmpZip :: (Manticore m) =>  [(Symbol, Tipo)] -> [(Symbol, Tipo, Int)] -> m Bool
cmpZip [] [] = return True
cmpZip [] _ = return False
cmpZip _ [] = return False
cmpZip ((sl,tl):xs) ((sr,tr,p):ys) = do
        b <- tiposIguales tl tr
        if b  && (sl == sr) then cmpZip xs ys
                else return False

buscarM :: Symbol -> [(Symbol, Tipo, Int)] -> Maybe Tipo
buscarM s [] = Nothing
buscarM s ((s',t,_):xs) | s == s' = Just t
                        | otherwise = buscarM s xs

transVar :: (Manticore w) => Var -> w Tipo
transVar (SimpleVar s) = getTipoValV s
transVar (FieldVar v s) = do 
        v' <- transVar v
        case v' of
            TRecord xs _ -> case buscarM s xs of
                Just t -> return t
                _ -> E.error $ internal $ T.pack $ "record: el campo " ++ T.unpack s ++" no está definido"
            x -> E.error $ internal $ T.pack $ "record: la variable no tiene tipo record sino " ++ show x 
transVar (SubscriptVar v e) = do
        e' <- transExp e
        C.unlessM (tiposIguales e' $ TInt RW) $ E.error $ internal $ T.pack $ "array: el indice no es un entero"
        v' <- transVar v
        case v' of 
            TArray t _ -> return t
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

transDec :: (Manticore w) => Dec -> w () -- por ahora...
transDec (TypeDec ls) = addTypos ls
transDec w@(VarDec s mb Nothing init p) = do
    tinit <- transExp init
    case tinit of
        TNil -> errorTT p (ppD w) "declaracion: se intento asignar Nil a una variable sin signatura de tipo" 
        TInt RO -> insertValV s (TInt RW)
        t -> insertValV s t

transDec w@(VarDec s mb (Just t) init p) = do
    tinit <- transExp init
    t' <- getTipoT t
    C.unlessM (tiposIguales t' tinit) 
        (errorTT p (ppD w) $ "se esperaba valor de tipo " ++ 
                           show t' ++ " y se tiene un valor de tipo " ++ show tinit)
    case tinit of
        TInt RO -> insertValV s (TInt RW)
        t -> insertValV s t
   

transDec w@(FunctionDec fb) = do
    mapM_ (\(s, flds, ms, e, p) -> do
        u <- ugen
        flds' <- mapM (\(_,_,ty) -> transTy ty) flds
        label <- genLabel s p u
        case ms of
            Nothing -> insertFunV s  (u, label, flds', TUnit, False)      
            Just rt -> do
                rt' <- getTipoT rt
                insertFunV s (u, label, flds', rt', False)
        ) fb  
    mapM_ (\(s, flds, ms, e, p) -> do
       (u,label,ts,tr,_) <- getTipoFunV s
       setRPoint
       mapM_ (\((s,_,_),t) -> insertValV s t) (zip flds ts)
       e' <- transExp e
       C.unlessM (tiposIguales e' tr) (errorTT p (ppD w) $ "se esperaba que el tipo del cuerpo de la funcion " ++
                                                            show s ++ " fuera " ++ show tr ++ " y se tiene " ++ show e')
       restoreRPoint
       ) fb
     
transExp :: (Manticore w) => Exp -> w Tipo
transExp w@(VarExp v p) = addpos (transVar v) p w
transExp (UnitExp {}) = return TUnit
transExp (NilExp {}) = return TNil
transExp (IntExp {}) = return $ TInt RW
transExp (StringExp {}) = return TString
transExp w@(CallExp nm args p) = do 
        (_,_,ts,tr,_) <- getTipoFunV nm
        C.unless (P.length ts == P.length args) $ errorTT p (ppE w) $ "llamada a funcion " ++ T.unpack nm ++ ": numero de argumentos erroneo"
        let checkTypes t e = do -- armo una función que compara un tipo esperado con el
            t' <- transExp e    -- calculado recursivamente, sale con error si falla
            ifM (tiposIguales t t') (return t)
                (errorTT p (ppE w) $ "llamada a funcion " ++ T.unpack nm ++ ": tipo de argumento invalido, se esperaba "
                           ++ show t ++ " pero se encontro " ++ show t')
        types <- zipWithM checkTypes ts args
        return tr
transExp w@(OpExp el' oper er' p) = do -- Esta va gratis
        el <- transExp el'
        er <- transExp er'
        C.unlessM (tiposIguales el er) (errorTT p (ppE w) ("tipos " ++ show el ++ " y " ++ show er ++ " no son comparables"))
        case oper of
            EqOp  -> do
                    C.unless (okOp el er oper) (errorTT p (ppE w) ("tipos " ++ show el ++ " y " ++ show er ++ " no son comparables mediante " ++ show oper))
                    return $ TInt RW
            NeqOp -> do
                    C.unless (okOp el er oper) (errorTT p (ppE w) ("tipos " ++ show el ++ " y " ++ show er ++ " no son comparables mediante " ++ show oper))
                    return $ TInt RW
            PlusOp -> do
                    C.unlessM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("tipos " ++ show el' ++ " no es un entero"))
                    return $ TInt RW
            MinusOp ->do
                     C.unlessM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("tipos " ++ show el' ++ " no es un entero"))
                     return $ TInt RW
            TimesOp -> do
                        C.unlessM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("tipos " ++ show el' ++ " no es un entero"))
                        return $ TInt RW
            DivideOp -> do  
                    C.unlessM (tiposIguales el $ TInt RW) (errorTT p (ppE w) ("tipos " ++ show el' ++ " no es un entero"))
                    return $ TInt RW
            LtOp -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                           (return $ TInt RW )
                           (errorTT p (ppE w) ("elementos de tipo" ++ show el ++ " no son comparables"))
            LeOp -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                           (return $ TInt RW)
                           (errorTT p (ppE w) ("elementos de tipo" ++ show el ++ " no son comparables"))
            GtOp -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                            (return $ TInt RW )
                            (errorTT p (ppE w) ("elementos de tipo" ++ show el ++ " no son comparables"))
            GeOp -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                            (return $ TInt RW) 
                            (errorTT p (ppE w) ("elementos de tipo" ++ show el ++ " no son comparables"))

transExp w@(RecordExp flds rt p) = do  -- Se debe respetar el orden de los efectos
    rType <- getTipoT rt  -- busco el tipo de record en el entorno
    case rType of
        TRecord decFlds _ -> do
                typedFlds <- mapM (\(s, e) -> transExp e >>= \et -> return (s, et)) flds -- encuentro el tipo de cada field
                let sortedFlds = sortBy (comparing fst) typedFlds   -- ordeno los campos tipados, suponiendo que fueron parseados en orden
                ifM (cmpZip sortedFlds decFlds) (return rType)      -- comparo que cada campo encontrado tenga el tipo que fue declarado 
                    (errorTT p (ppE w) $ "record invalido, se esperaba: " ++ show decFlds
                               ++ " pero se encontro: " ++ show typedFlds)
        _ -> errorTT p (ppE w) $ "se esperaba un record, pero se encontro: " ++ show rt

transExp (SeqExp es p) = do -- Va gratis
        es' <- mapM transExp es
        return $ last es'

transExp w@(AssignExp var exp p) = do
    var' <- transVar var
    exp' <- transExp exp
    matches <- tiposIguales var' exp'
    if not matches
        then errorTT p (ppE w) $ "asignacion: se esperaba valor de tipo " ++ show var' ++ " y se tiene valor de tipo " ++ show exp'
        else if var' == (TInt RO)
            then errorTT p (ppE w) "asignacion: se intento asignar una variable RO"
            else return TUnit

transExp w@(IfExp co th Nothing p) = do
        co' <- transExp co
        C.unlessM (tiposIguales co' $ TInt RW) $ errorTT p (ppE w) $ "if: la condicion no es de tipo " ++ show (TInt RW)
        th' <- transExp th
        C.unlessM (tiposIguales th' TUnit) $ errorTT p (ppE w) $ "if: el cuerpo no es de tipo " ++ show TUnit
        return TUnit

transExp w@(IfExp co th (Just el) p) = do 
        co' <- transExp co
        C.unlessM (tiposIguales co' $ TInt RW) $ errorTT p (ppE w) $ "if: la condicion no es de tipo " ++ show (TInt RW)
        th' <- transExp th
        el' <- transExp el
        C.unlessM (tiposIguales th' el') $ errorTT p (ppE w) "if: las ramas tienen distinto tipo"
        return th'

transExp w@(WhileExp co body p) = do
        co' <- transExp co
        C.unlessM (tiposIguales co' $ TInt RW) $ errorTT p (ppE w) $ "while: la condicion no es de tipo " ++ show (TInt RW)
        body' <- transExp body
        C.unlessM (tiposIguales body' TUnit) $ errorTT p (ppE w) $ "while: el cuerpo no es de tipo " ++ show TUnit
        return TUnit

transExp w@(ForExp nv mb lo hi bo p) = do
        lo' <- transExp lo
        C.unlessM (tiposIguales lo' $ TInt RW) $ errorTT p (ppE w) $ "for: la cota inferior no es de tipo " ++ show (TInt RW)
        hi' <- transExp hi
        C.unlessM (tiposIguales hi' $ TInt RW) $ errorTT p (ppE w) $ "for: la cota superior no es de tipo " ++ show (TInt RW)
        setRPoint 
        insertVRO nv (TInt RO)
        bo' <- transExp bo
        C.unlessM (tiposIguales bo' $ TUnit) $ errorTT p (ppE w) $ "for: el cuerpo no es de tipo " ++ show TUnit
        restoreRPoint
        return TUnit

transExp(LetExp dcs body p) = do -- Va gratis...
        setRPoint
        mapM_ transDec dcs -- esto se deberá modificar al momento de generar cod intermedio.
        b <- transExp body
        restoreRPoint
        return b

transExp(BreakExp p) = return TUnit -- Va gratis ;)

transExp w@(ArrayExp sn cant init p) = do
        sn' <- getTipoT sn
        init' <- transExp init
        cant' <- transExp cant
        C.unlessM (tiposIguales cant' (TInt RW)) $ errorTT p (ppE w) $ "array: el tamaño no es de tipo " ++ show (TInt RW) 
        case sn' of
            TArray t _ -> do
                C.unlessM (tiposIguales t init') $ errorTT p (ppE w) $ "array: se declaro de tipo " ++ show t ++ " y se lo intento inicializar con tipo " ++ show init'
                return sn' 
            x -> errorTT p (ppE w) $ "array: el tipo " ++ show x ++  " no es un array"


