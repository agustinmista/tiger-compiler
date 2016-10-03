module Main (main) where
import           Control.Monad
import           Control.Monad.State.Lazy
import           Data.Either
import           Data.Maybe
import           System.Console.GetOpt
import qualified System.Environment       as Env
import           System.Exit

import           TigerAbs
import           TigerCanon
import           TigerEscap
import           TigerFrame
import           TigerParser
import           TigerPretty
import           TigerSeman
import           TigerTrans
import qualified TigerTree                as Tree

import           TigerPrettyIr

import           Text.Parsec              (runParser)

data Options = Options
        {optArbol    :: Bool
        ,optDebEscap :: Bool
        ,optIr       :: Bool
        ,optCanon    :: Bool
    }
    deriving Show

data GenEstate = GE {tempseed :: Int, labelseed :: Int}
type GenSt = StateT GenEstate IO

initState = GE {tempseed = 0, labelseed = 0}

{-
   #if __GLASGOW_HASKELL__ <= 761
   isLeft :: Either a b -> Bool
   isLeft (Left _) = True
   isLeft _ = False
   #endif
-}


getLabel :: GenSt Int
getLabel = do
    st <- get
    return (labelseed st)

getTemp :: GenSt Int
getTemp = do
    st <- get
    return (tempseed st)

setLabel :: Int -> GenSt ()
setLabel l = do
    st <- get
    put $ st{labelseed = l}

setTemp:: Int -> GenSt ()
setTemp t = do
    st <- get
    put $ st{tempseed = t}

defaultOptions :: Options
defaultOptions = Options {optArbol = False, optDebEscap = False, optIr = False, optCanon = False}

options :: [OptDescr (Options -> Options)]
options =   [ Option ['a'] ["arbol"] (NoArg (\opts -> opts {optArbol = True})) "Muestra el AST luego de haber realizado el cálculo de escapes"
            , Option ['e'] ["escapada"] (NoArg (\opts -> opts {optDebEscap = True})) "Stepper escapadas"
            , Option ['i'] ["ir"] (NoArg (\opts -> opts {optIr = True})) "Muestra el código intermedio"
            , Option ['c'] ["canon"] (NoArg (\opts -> opts {optCanon = True})) "Muestra el código intermedio canonizado"]

compilerOptions :: [String] -> IO (Options, [String])
compilerOptions argv = case getOpt Permute options argv of
                        (o,n,[]) -> return (foldl (flip id) defaultOptions o, n)
                        (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
    where
        header = "Se usa: tiger fileName [OPTIONS] "

showExp :: Exp -> IO ()
showExp e = do
    putStrLn "Mostramos el AST (PP Gracias a Emilio Lopez Junior)"
    putStrLn $ renderExp e

calculoEscapadas :: Exp -> Options -> IO (Maybe Exp)
calculoEscapadas rawAST opt =
                if optDebEscap opt then
                    case debbugEnv rawAST of
                    (Left errEsc) -> do
                        print "Error en el calculo de variables escapadas:"
                        print errEsc
                        return Nothing
                    (Right (exp,envs)) -> do
                        putStrLn "Stepper MODE!!! Bienvenidos a la fiesta de las variables escapadas"
                        mapM_ ((\str -> putStrLn str >> putStrLn "-------") . show) (reverse (e envs))
                        putStrLn "yes!!!"
                        return (Just exp)
                else
                    case calcularEEsc rawAST of
                        (Left errEsc) -> do
                            putStrLn "Error en el calculo de variables escapadas:"
                            print errEsc
                            return Nothing
                        (Right escap) -> do
                            when (optArbol opt) (showExp escap)
                            putStrLn "yes!!!"
                            return $ Just escap

--isLeft :: Either a b -> Bool
--isLeft (Left _) = True
--isLeft _ = False
--
getLeft :: Either a b -> a
getLeft (Left x) = x
getLeft _ = error "no hay izq"
--
getRight :: Either a b -> b
getRight (Right x) = x
getRight _ = error "no hay derecho"

codgenStep :: Exp -> Bool -> GenSt [Frag]
codgenStep e s = do
    let sem = runLion e
    when (isLeft sem) (error $ "Semantic core:"++ show (getLeft sem))
    let (fs,temp,lbl) = getRight sem
    when s (lift $ putStrLn $ foldr (\t ts -> renderFrag t ++ '\n':ts) "" fs)
    setLabel lbl
    setTemp temp
    return fs

canonStep' :: [Frag] -> GenSt ([Frag],[([Tree.Stm],Frame)])
canonStep' xs = do
    l <- getLabel
    t <- getTemp
    let (strs, procs) =  sepFrag xs
    let (can, t', l') = canon t l procs
    setLabel l'
    setTemp t'
    return (strs, can)

canonStep :: [Frag] -> Bool -> GenSt ([Frag],[([Tree.Stm],Frame)])
canonStep xs opt = do
    (strs, procs) <- canonStep' xs
    when opt ( -- Show Time!
        lift $ putStrLn "Data Segment:" >>
        mapM_ (putStrLn . renderFrag) strs >>
        putStrLn "Code Segment:" >>
        mapM_ (\(sts,fr) -> putStrLn $ renderPCan sts fr) procs)
    return (strs,procs)

main = do
    s:opts <- Env.getArgs
    (opts', err) <- compilerOptions opts
    sourceCode <- readFile s
    let rawEAST = runParser expression () s sourceCode
    when (isLeft rawEAST) (error $ "Parser error..." ++ show (getLeft rawEAST))
    east <- calculoEscapadas (getRight rawEAST) opts'
    when (isNothing east) (error "Calculo escapadas")
    -- let semantico = runLion $ fromJust east
    codecanon <- evalStateT (do
            frags <- codgenStep (fromJust east) (optIr opts')
            canonStep frags (optCanon opts')) initState
    print "Genial!"
