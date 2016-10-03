{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}
module TigerSeman where

import           TigerAbs
import           TigerEnv
import           TigerErrores         as E
import           TigerSres
import           TigerTemp
import           TigerTips
import           TigerTrans

import           Control.Arrow
import           Control.Conditional  as C
import           Control.Monad
import           Control.Monad.Except
import qualified Control.Monad.State  as ST
import           Data.List            as List
import qualified Data.Map.Strict      as M
import           Data.Maybe
import           Data.Ord
import           Prelude              as P

import qualified Data.Graph           as G
import qualified Data.Text            as T

import           Debug.Trace

-- | Clase general que propongo para realizar el análisis semántico.
class (NotFounder w, TLGenerator w) => Manticore w where
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
    --
    -- | Función para retornar errores de tipos con mensaje particular.
    errorTT :: Pos -> String -> w a
    errorTT p msg = E.error $ internal $ T.pack $ "Error de tipos:\n" ++ msg ++ " en la pos" ++ show p
    -- | Función de Debugging que muestra el entorno de valores
    showVEnv :: w ()
    -- | Función de Debugging que muestra el entorno de tipos
    showTEnv :: w ()
    -- | Debugging entrega 2
    showEnt2 :: w ()
    --  | Tiposiguales, es relativo y necesario por la definición de 'Tipo' que
    --  propuse en TigerTips.hs . Viene gratis...
    tiposIguales :: Tipo -> Tipo -> w Bool
    tiposIguales (RefRecord s) l@(TRecord _ u) = do
        st <- getTipoT s
        case st of
            TRecord _ u1 -> return (u1 == u)
            ls@(RefRecord s') -> tiposIguales ls l
            _ -> E.error $ internal $ T.pack "No son tipos iguales... 123+1"
    tiposIguales l@(TRecord _ u) (RefRecord s) = do
        st <- getTipoT s
        case st of
            TRecord _ u1 -> return (u1 == u)
            ls@(RefRecord s') -> tiposIguales l ls
            _ -> E.error $ internal $ T.pack "No son tipos iguales... 123+2"
    tiposIguales (RefRecord s) (RefRecord s') = do
        s1 <- getTipoT s
        s2 <- getTipoT s'
        tiposIguales s1 s2
    tiposIguales TNil  (RefRecord _) = return True
    tiposIguales (RefRecord _) TNil = return True
    tiposIguales (RefRecord _) _ = E.error $ internal $ T.pack "No son tipos iguales... 123+3"
    tiposIguales  e (RefRecord s) = E.error $ internal $ T.pack $ "No son tipos iguales... 123+4" ++ (show e ++ show s)
    tiposIguales a b = return (intiposIguales a b)
    --
    -- | Generador de 'Unique' para las definiciones de los tipos records,
    -- array, etc.
    ugen :: w Unique


-- | Función que nos permite agregar un batch de tipos al entorno, buscando
-- los ciclos. À la Guido, utilice un sort topológico, que primero construye
-- un grafo con las dependencias y luego llamo a la librería.
addTypos :: Manticore w => [(Symbol, Ty, Pos)] -> w ()
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
transVar (SimpleVar s) = error "COMPLETAR"
transVar (FieldVar v s) = error "COMPLETAR"
transVar (SubscriptVar v e) = error "Completar"

transTy :: (Manticore w) => Ty -> w Tipo
transTy (NameTy s) = error "COMPLETAR"
transTy (RecordTy flds) = error "COMPLETAR"
transTy (ArrayTy s) = error "COMPLETAR"

fromTy :: (Manticore w) => Ty -> w Tipo
fromTy (NameTy s) = error "COMPLETAR"
fromTy _ = error "COMPLETAR"

transDec :: (Manticore w, FlorV w) => Dec -> w [BExp] -- por ahora...
transDec (FunctionDec fb) = error "COMPLETAR"
transDec (VarDec s mb mty init p) = error "COMPLETAR"
transDec (TypeDec ls ) = error "COMPLETAR"

transExp :: (Manticore w, FlorV w) => Exp -> w (BExp, Tipo)
transExp (VarExp v p) = addpos (transVar v) p
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
transExp (CallExp nm args p) = error "COMPLETAR"
transExp (OpExp el' oper er' p) = do
        (cl,el) <- transExp el'
        (cr,er) <- transExp er'
        ifNM (tiposIguales el er) (errorTT p ("OpExp:Tipos diferentes" ++ show el ++ show er))
         $  case oper of
                EqOp  ->
                        if (okOp el er oper)
                        then do
                                c <- ifM (tiposIguales el TString) (binOpStrExp cl oper cr) (binOpIntRelExp cl oper cr)
                                return (c,TInt RW)
                        else (errorTT p ("Tipos no comparables " ++ show el ++ show er ++ show oper))
                NeqOp ->
                        if (okOp el er oper)
                        then do
                                c <- ifM (tiposIguales el TString) (binOpStrExp cl oper cr) (binOpIntRelExp cl oper cr)
                                return (c,TInt RW)
                        else (errorTT p ("Tipos no comparables " ++ show el ++ show er ++ show oper))
                PlusOp ->
                        ifNM (tiposIguales el $ TInt RW) (errorTT p ("Tipo " ++ show el' ++ " no es un entero"))
                        $ binOpIntExp cl oper cr >>= \c -> return (c,TInt RW)
                MinusOp ->
                         ifNM (tiposIguales el $ TInt RW) (errorTT p ("Tipo " ++ show el' ++ " no es un entero"))
                         $ binOpIntExp cl oper cr >>= \c -> return (c,TInt RW)
                TimesOp -> ifNM (tiposIguales el $ TInt RW) (errorTT p ("Tipo " ++ show el' ++ " no es un entero"))
                            $ binOpIntExp cl oper cr >>= \c -> return (c,TInt RW)
                DivideOp ->
                        ifNM (tiposIguales el $ TInt RW) (errorTT p ("Tipo " ++ show el' ++ " no es un entero"))
                        $ binOpIntExp cl oper cr >>= \c -> return (c,TInt RW)
                _ -> ifM (tiposIguales el $ TInt RW)
                                (do
                                    c <- binOpIntRelExp cl oper cr
                                    return (c, TInt RW))
                                (ifM (tiposIguales el TString)
                                    (do
                                        c <- binOpStrExp cl oper cr
                                        return (c, TInt RW))
                                    (errorTT p ("Elementos de tipo" ++ show el ++ "no son comparables")))
transExp(RecordExp flds rt p) = do -- COMPLETAR. Respetar el orden de los efecto...
        recTy <- addpos (getTipoT rt) p -- Buscamos el tipo de rt
        case recTy of -- Chequeamos que el tipo real sea Record...
            TRecord rflds _ -> do
                flds'' <- mapM (\(s,e) -> do {(ce,e') <- transExp e; return ((ce,s),(s,e'))}) flds
                let (cds,flds') = unzip flds''
                let sflds = List.sortBy (comparing fst) flds'
                -- Asumimos que estan ordenados los campos del record.
                (m, b) <- cmpZip flds' rflds
                if b
                    then do
                        c <- recordExp (map (\(cb,s) -> (cb,m M.! s)) cds)
                        return (c, recTy)
                    else (errorTT p $ "Error en los campos del records..." ++ show flds' ++ show rflds)
            _ -> errorTT p ("El tipo[" ++ show rt ++ "NO es un record")
transExp(SeqExp es p) = do
        es' <- mapM transExp es
        let ess = map fst es'
        let (_,ty) = last es'
        c <- seqExp ess
        return (c,ty)
transExp(AssignExp var val p) = error "COMPLETAR"
transExp(IfExp co th Nothing p) = do
        (cco,co') <- transExp co
        ifM (not <$> tiposIguales co' (TInt RW)) (errorTT p "Error en la condición")
            $ transExp th >>= \(cth,th') ->
                ifM (not <$> tiposIguales th' TUnit) (errorTT p "La expresión del then no es de tipo unit")
                 $ ifThenExp cco cth >>= \c -> return (c,TUnit)
transExp(IfExp co th (Just el) p) = do
        (cco,co') <- transExp co
        ifNM (tiposIguales co' $ TInt RW) (errorTT p "Error en la condición")
            $   do
                    (cth,th') <- transExp th
                    (cel,el') <- transExp el
                    ifNM (tiposIguales th' el') (errorTT p "Los branches tienen diferentes tipos...")
                        $ ifThenElseExp cco cth cel >>= \c -> return (c,th')
transExp(WhileExp co body p) = do -- TODO COMPLETAR
        (cco,co') <- transExp co
        ifNM (tiposIguales co' $ TInt RW) (errorTT p "La condición no es un booleano")
            $
            preWhileforExp >>
            transExp body >>= \(cb,body') ->
            ifNM (tiposIguales body' TUnit) (errorTT p "El body del while no es de tipo unit...")
            $ do
                lvl <- topLevel
                c <- whileExp cco cb
                posWhileforExp
                return (c,TUnit)
transExp(ForExp nv mb lo hi bo p) = error "COMPLETAR"
transExp(LetExp dcs body p) = do
        setRPoint
        dcs' <- mapM transDec dcs
        let dcs'' = concat dcs'
        (cb,b) <- transExp body
        c <- letExp dcs'' cb
        restoreRPoint
        return (c,b)
transExp(BreakExp p) = error "COMPLETAR"
transExp(ArrayExp sn cant init p) = error "COMPLETAR"
