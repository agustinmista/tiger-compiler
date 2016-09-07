{-# LANGUAGE TypeSynonymInstances,FlexibleInstances, TypeFamilies #-}
module TigerSeman where

import TigerSres
import TigerTips
import TigerEnv
import TigerErrores as E
import TigerAbs

import qualified Data.Map.Strict as M
import qualified Control.Monad.State as ST
import Control.Monad
import Control.Arrow
import Control.Monad.Except
import Control.Conditional as C
import Data.List as List
import Data.Ord
import Prelude as P 

import qualified Data.Graph as G
import qualified Data.Text as T

import Debug.Trace

class (Environmental w, NotFounder w) => Manticore w where
-- Que compartan el espacio de nombres es decisión de la instancia.
    insertValV :: Symbol -> ValEntry -> w ()
    insertFunV :: Symbol -> FunEntry -> w ()
    insertVRO :: Symbol -> w ()
    insertTipoT :: Symbol -> Tipo -> w ()
    getTipoFunV :: Symbol -> w FunEntry 
    getTipoValV :: Symbol -> w ValEntry
    getTipoT :: Symbol -> w Tipo
    --
    setRPoint :: w ()
    restoreRPoint :: w ()
    --
    errorTT :: Pos -> String -> w a
    errorTT p msg = E.error $ internal $ T.pack $ "Error de tipos:\n" ++ msg ++ " en la pos" ++ show p
    showVEnv :: w ()
    showTEnv :: w ()
    --
    tiposIguales :: Tipo -> Tipo -> w Bool 
    tiposIguales (RefRecord s) l@(TRecord _ u) = do
        st <- getTipoT s
        case st of
            TRecord _ u1 -> return (u1 == u)
            ls@(RefRecord s') -> tiposIguales ls l
            _ -> E.error $ internal $ T.pack $ "No son tipos iguales... 123+1"
    tiposIguales l@(TRecord _ u) (RefRecord s) = do
        st <- getTipoT s
        case st of
            TRecord _ u1 -> return (u1 == u)
            ls@(RefRecord s') -> tiposIguales l ls 
            _ -> E.error $ internal $ T.pack $ "No son tipos iguales... 123+2"
    tiposIguales (RefRecord s) (RefRecord s') = do
        s1 <- getTipoT s
        s2 <- getTipoT s'
        tiposIguales s1 s2
    tiposIguales TNil  (RefRecord _) = return True
    tiposIguales (RefRecord _) TNil = return True
    tiposIguales (RefRecord _) _ = E.error $ internal $ T.pack $ "No son tipos iguales... 123+3"
    tiposIguales  e (RefRecord s) = E.error $ internal $ T.pack $ "No son tipos iguales... 123+4" ++ (show e ++ show s)
    tiposIguales a b = return (intiposIguales a b)
    --
    ugen :: w Unique -- unique generator
    --
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

addpos t p = handle t  (\t -> E.error $ adder t (T.pack $ show p))
-- Un ejemplo de estado que alcanzaría para realizar todas la funciones es:
-- data EstadoG = G {unique :: Int, vEnv :: [M.Map Symbol EnvEntry], tEnv :: [M.Map Symbol Tipo]}
--     deriving Show
--
-- Acompañado de un tipo de errores
-- data SEErrores = NotFound T.Text | DiffVal T.Text | Internal T.Text
--     deriving Show
--
--  Podemos definir el estado inicial como:
-- initConf :: EstadoG
-- initConf = G {unique = 0
--             , tEnv = [M.insert (T.pack "int") (TInt RW) (M.singleton (T.pack "string") TString)]
--             , vEnv = [M.fromList
--                     [(T.pack "print", Func (1,T.pack "print",[TString], TUnit, True))
--                     ,(T.pack "flush", Func (1,T.pack "flush",[],TUnit, True))
--                     ,(T.pack "getchar",Func (1,T.pack "getchar",[],TString,True))
--                     ,(T.pack "ord",Func (1,T.pack "ord",[TString],TInt RW,True)) -- Ojota con este intro...
--                     ,(T.pack "chr",Func (1,T.pack "chr",[TInt RW],TString,True))
--                     ,(T.pack "size",Func (1,T.pack "size",[TString],TInt RW,True))
--                     ,(T.pack "substring",Func (1,T.pack "substring",[TString,TInt RW, TInt RW],TString,True))
--                     ,(T.pack "concat",Func (1,T.pack "concat",[TString,TString],TString,True))
--                     ,(T.pack "not",Func (1,T.pack "not",[TInt RW],TInt RW,True))
--                     ,(T.pack "exit",Func (1,T.pack "exit",[TInt RW],TUnit,True))
--                     ]]}
-- Utilizando alguna especia de run de la monada definida, obtenemos algo así
--runLion :: Exp -> Either SEErrores Tipo 
--runLion e = run (transExp e) initConf

depend :: Ty -> [Symbol]
depend (NameTy s) = [s]
depend (ArrayTy s) = [s]
depend (RecordTy ts) = concatMap (\(_,_,t) -> depend t) ts


okOp :: Tipo -> Tipo -> Oper -> Bool
okOp TNil TNil EqOp = False
okOp TUnit _ EqOp = False
okOp _ _ EqOp = True
okOp TNil TNil NeqOp = False
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
		TRecord xs _ ->
			case buscarM s xs of
				Just t -> return t
				_ -> E.error $ internal $ T.pack $ "El campo no está definido"
		_ -> E.error $ internal $ T.pack $ "La variable no tiene tipo record" 

transVar (SubscriptVar v e) = do
	e' <- transExp e
	C.unlessM (tiposIguales e' $ TInt RW) $ E.error $ internal $ T.pack $ "El indice no es un entero"
	v' <- transVar v
	case v' of 
		TArray t _ -> return t
		_ -> E.error $ internal $ T.pack $ "La variable no tiene tipo record" 

transTy :: (Manticore w) => Ty -> w Tipo
transTy (NameTy s) = return TUnit -- Completar
transTy (RecordTy flds) = return TUnit -- Completar
transTy (ArrayTy s) = return TUnit -- Completar

fromTy :: (Manticore w) => Ty -> w Tipo
fromTy (NameTy s) = getTipoT s
fromTy _ = P.error "no debería haber una definición de tipos en los args..."

transDec :: (Manticore w) => Dec -> w () -- por ahora...
transDec (FunctionDec fb) = return ()
transDec (VarDec s mb mty init p) = return ()
transDec (TypeDec ls ) = return ()
       

transExp :: (Manticore w) => Exp -> w Tipo
transExp (VarExp v p) = addpos (transVar v) p
transExp (UnitExp {}) = return TUnit
transExp (NilExp {}) = return TNil
transExp (IntExp {}) = return $ TInt RW
transExp (StringExp {}) = return TString
transExp (CallExp nm args p) = do 
        (_,_,ts,tr,_) <- getTipoFunV nm
       	C.unless (P.length ts == P.length args) $ errorTT p "Numero de argumentos erroneo"
	let checkTypes t e = do -- armo una función que compara un tipo esperado con el
            t' <- transExp e    -- calculado recursivamente, sale con error si falla
            ifM (tiposIguales t t') (return t)
                (errorTT p $ "Tipo de argumento invalido, se esperaba "
                           ++ show t ++ "pero se encontro" ++ show t')
        types <- zipWithM checkTypes ts args
        return tr
       
transExp (OpExp el' oper er' p) = do -- Esta va gratis
        el <- transExp el'
        er <- transExp er'
        C.unlessM (tiposIguales el er) (errorTT p "Tipos diferentes")
        case oper of
            EqOp  -> do
                    C.unless (okOp el er oper) (errorTT p ("Tipos no comparables " ++ show el ++ show er ++ show oper))
                    return $ TInt RW
            NeqOp -> do
                    C.unless (okOp el er oper) (errorTT p ("Tipos no comparables " ++ show el ++ show er ++ show oper))
                    return $ TInt RW
            PlusOp -> do
                    C.unlessM (tiposIguales el $ TInt RW) (errorTT p ("Tipo " ++ show el' ++ " no es un entero"))
                    return $ TInt RW
            MinusOp ->do
                     C.unlessM (tiposIguales el $ TInt RW) (errorTT p ("Tipo " ++ show el' ++ " no es un entero"))
                     return $ TInt RW
            TimesOp -> do
                        C.unlessM (tiposIguales el $ TInt RW) (errorTT p ("Tipo " ++ show el' ++ " no es un entero"))
                        return $ TInt RW
            DivideOp -> do  
                    C.unlessM (tiposIguales el $ TInt RW) (errorTT p ("Tipo " ++ show el' ++ " no es un entero"))
                    return $ TInt RW
            LtOp -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                           (return $ TInt RW )
                           (errorTT p ("Elementos de tipo" ++ show el ++ "no son comparables"))
            LeOp -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                           (return $ TInt RW)
                           (errorTT p ("Elementos de tipo" ++ show el ++ "no son comparables"))
            GtOp -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                            (return $ TInt RW )
                            (errorTT p ("Elementos de tipo" ++ show el ++ "no son comparables"))
            GeOp -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                            (return $ TInt RW) 
                            (errorTT p ("Elementos de tipo" ++ show el ++ "no son comparables"))

transExp (RecordExp flds rt p) = do
    rType <- getTipoT rt  -- busco el tipo de record en el entorno
    case rType of
        TRecord decFlds _ -> do
                typedFlds <- mapM (\(s, e) -> transExp e >>= \et -> return (s, et)) flds -- encuentro el tipo de cada field
                let sortedFlds = sortBy (comparing fst) typedFlds   -- ordeno los campos tipados, suponiendo que fueron parseados en orden
                ifM (cmpZip sortedFlds decFlds) (return rType)      -- comparo que cada campo encontrado tenga el tipo que fue declarado 
                    (errorTT p $ "Record invalido, se esperaba: " ++ show decFlds
                               ++ " pero se encontro: " ++ show typedFlds)
        _ -> errorTT p $ "Se esperaba un record, pero se encontro: " ++ show rt

transExp(SeqExp es p) = do -- Va gratis
        es' <- mapM transExp es
        return $ last es'

transExp(AssignExp var val p) = do
	var' <- transVar var
	C.unlessM (tiposIguales var' $ TInt RO) $ errorTT p "Se intento asignar una variable RO"
	val' <- transExp val
	C.unlessM (tiposIguales var' val') $ errorTT p "Error de tipos en la asignacion"
	return TUnit	

transExp(IfExp co th Nothing p) = do
        co' <- transExp co
        C.unlessM (tiposIguales co' $ TInt RW) $ errorTT p "Error en la condición"
        th' <- transExp th
        C.unlessM (tiposIguales th' TUnit) $ errorTT p "La expresión del then no es de tipo unit"
        return TUnit

transExp(IfExp co th (Just el) p) = do 
        co' <- transExp co
        C.unlessM (tiposIguales co' $ TInt RW) $ errorTT p "Error en la condición"
        th' <- transExp th
        el' <- transExp el
        C.unlessM (tiposIguales th' el') $ errorTT p "Las ramas del if tienen distinto tipo"
        return th'

transExp(WhileExp co body p) = do
        co' <- transExp co
        C.unlessM (tiposIguales co' $ TInt RW) $ errorTT p "Error en la condición"
        body' <- transExp body
        C.unlessM (tiposIguales body' TUnit) $ errorTT p "La expresión del while no es de tipo unit"
        return TUnit

transExp(ForExp nv mb lo hi bo p) = do
	lo' <- transExp lo
	C.unlessM (tiposIguales lo' $ TInt RW) $ errorTT p "Error en la cota inferior"
	hi' <- transExp hi
	C.unlessM (tiposIguales hi' $ TInt RW) $ errorTT p "Error en la cota superior"
	setRPoint 
	insertVRO nv
	bo' <- transExp bo
	C.unlessM (tiposIguales bo' $ TUnit) $ errorTT p "Cuerpo del for no es de tipo Unit"	
	restoreRPoint
	return TUnit	

transExp(LetExp dcs body p) = do -- Va gratis...
        setRPoint
        mapM_ transDec dcs -- esto se deberá modificar al momento de generar cod intermedio.
        showTEnv 
        b <- transExp body
        restoreRPoint
        return b

transExp(BreakExp p) = return TUnit -- Va gratis ;)

transExp(ArrayExp sn cant init p) = do
	sn' <- getTipoT sn
	init' <- transExp init
	cant' <- transExp cant
	C.unlessM (tiposIguales cant' (TInt RW)) $ errorTT p "El tamaño del arreglo no es un entero" 
	case sn' of
		TArray t _ -> do
			C.unlessM (tiposIguales t init') $ errorTT p "El tipo del arreglo no coincide con el inicial"
			return sn' 
		_ -> errorTT p "El tipo no es un array"
		 




