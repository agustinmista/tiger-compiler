module Main (main) where
import qualified System.Environment as Env
import System.Exit
import System.Console.GetOpt
import Control.Monad
import Data.Maybe
import Data.Either

import TigerAbs
import TigerParser
import TigerEscap
import TigerPretty
import TigerSeman

import Text.Parsec (runParser)

data Options = Options {
        optArbol :: Bool,
        optDebEscap :: Bool
    } deriving Show


defaultOptions :: Options
defaultOptions = Options {optArbol = False, optDebEscap = False }


options :: [OptDescr (Options -> Options)]
options = [ Option ['a'] ["arbol"] (NoArg (\opts -> opts {optArbol = True})) "Muestra el AST luego de haber realizado el cálculo de escapes"
            , Option ['e'] ["escapada"] (NoArg (\opts -> opts {optDebEscap = True})) "Stepper escapadas"]

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
                if (optDebEscap opt) then
                    case (debbugEnv rawAST) of
                    (Left errEsc) -> do
                        putStrLn "Error en el calculo de variables escapadas:"
                        print errEsc
                        return Nothing
                    (Right (exp,envs)) -> do
                        putStrLn "Stepper MODE!!! Bienvenidos a la fiesta de las variables escapadas"
                        mapM_ ((\str -> putStrLn str >> putStrLn "-------") . show) (reverse (e envs))
                        putStrLn "yes!!!"
                        return (Just exp)
                else
                    case (calcularEEsc rawAST) of
                        (Left errEsc) -> do
                            putStrLn "Error en el calculo de variables escapadas:"
                            print errEsc 
                            return Nothing
                        (Right escap) -> do
                            when (optArbol opt) (showExp escap)
                            (putStrLn "yes!!!")
                            return $ Just escap

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

getLeft :: Either a b -> a
getLeft (Left x) = x
getLeft _ = error "no hay izq"

getRight :: Either a b -> b
getRight (Right x) = x
getRight _ = error "no hay derecho"

main = do
    s:opts <- Env.getArgs
    (opts', err) <- compilerOptions opts
    sourceCode <- readFile s
    let rawEAST = runParser expression () s sourceCode
    putStrLn (show rawEAST)
    when (isLeft rawEAST) (error $ "Parser error..." ++ show (getLeft rawEAST))
    east <- calculoEscapadas (getRight rawEAST) opts'
    when (isNothing east) (error $ "Calculo escapadas")
--    let semantico = runLion $ fromJust east 
--    when (isLeft semantico) (error $ "Semantic core:"++ show (getLeft semantico))
    print "Genial!"
