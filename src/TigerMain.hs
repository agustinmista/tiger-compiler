module Main (main) where
import qualified System.Environment as Env
import System.Exit
import System.Console.GetOpt
import Control.Monad
import Data.Maybe
import Data.Either
import Control.Exception

import TigerAbs
import TigerParser
import TigerEscap
import TigerPretty
import TigerSeman

import Text.Parsec (runParser)

-- Opciones de compilacion
data Options = Options {
        optAST :: Bool,
        optEsc :: Bool
    } deriving Show

-- Opciones de compilación por defecto
defaultOptions :: Options
defaultOptions = Options {optAST = False, optEsc = False }

-- Descriptor de opciones de compilacion
options :: [OptDescr (Options -> Options)]
options = [ Option ['a'] ["ast"]    (NoArg (\opts -> opts {optAST = True})) "show AST after escape analysis",
            Option ['e'] ["escape"] (NoArg (\opts -> opts {optEsc = True})) "show escape analysis step by step"]

-- Parsea los argumentos de linea de comando, devuelve un mensaje de error
-- o una tupla con las opciones de compilacion y el archivo fuente
parseCommand :: [String] -> Either String (Options, String)
parseCommand argv = 
    case getOpt Permute options argv of
        (opt, [file], [])  -> Right (foldl (flip id) defaultOptions opt, file)
        (_, [], _)         -> Left  "No input file specified"
        (_, (_:_:_), _)    -> Left  "Too many input files"
        (_, _, errs@(_:_)) -> Left  (concat errs) 



-- Calculo de variables escapadas
calculoEscapadas :: Exp -> Options -> IO (Either Errores Exp)
calculoEscapadas rawAST opt = 
                if (optEsc opt) then
                    case (debbugEnv rawAST) of
                    (Left errEsc) -> return $ Left errEsc
                    (Right (exp,envs)) -> do
                        putStrLn "**** stepper mode begin ****"
                        mapM_ ((\str -> putStrLn str >> putStrLn "-------") . show) (reverse (e envs))
                        putStrLn "**** stepper mode end ****"
                        return (Right exp)
                else
                    case (calcularEEsc rawAST) of
                        (Left errEsc) -> return $ Left errEsc
                        (Right escap) -> do
                        when (optAST opt) (putStrLn (show escap) >> putStrLn (renderExp escap))
                        return $ Right escap


-- Helpers para desempaquetar either
fromLeft :: Either a b -> a
fromLeft (Left x) = x
fromLeft _ = error "called fromLeft with Right value"

fromRight :: Either a b -> b
fromRight (Right x) = x
fromRight _ = error "called fromRight with Left value"


-- Handler para excepciones
printException :: SomeException -> IO ()
printException e = putStrLn $ "tiger: " ++ show e


---------------------------------------------
--                  MAIN                   --
---------------------------------------------
main = handle printException $ do
    -- Parseo de argumentos de linea de comandos
    argv <- Env.getArgs
    let parsedArgv = parseCommand argv
    when (isLeft parsedArgv) (error $ fromLeft parsedArgv)
    let (opts, file) = fromRight parsedArgv
    sourceCode <- readFile file
    
    -- Parseo del archivo fuente
    let rawEAST = runParser expression () file sourceCode
    when (isLeft rawEAST) (error $ "error parsing " ++ show (fromLeft rawEAST))
    
    -- Calculo de variables escapadas
    east <- calculoEscapadas (fromRight rawEAST) opts
    when (isLeft east) (error $ "escape analysis error: \n\t" ++ show (fromLeft east))
    
    -- Analisis semantico
--    let semantico = runLion $ fromJust east 
--    when (isLeft semantico) (error $ "Semantic core:"++ show (fromLeft semantico))
    
    putStrLn "finished"
