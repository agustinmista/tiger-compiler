module TigerMain (main) where
import qualified System.Environment as Env
import System.Exit
import System.Console.GetOpt
import Control.Monad
import Data.Maybe
import Data.List
import Data.Either hiding (isLeft)
import Control.Exception

import TigerAbs
import TigerParser
import TigerEscap
import TigerPretty
import TigerSeman
import TigerPrettyIr

import Text.Parsec (runParser)
import Data.Map.Strict (toList)

-- Opciones de compilacion
data Options = Options {
        optSrc :: Bool,
        optAST :: Bool,
        optPPA :: Bool,
        optFgs :: Bool,
        optEsc :: Bool
    } deriving Show

-- Opciones de compilación por defecto
defaultOptions :: Options
defaultOptions = Options { optSrc = False
                         , optAST = False
                         , optPPA = False
                         , optFgs = False
                         , optEsc = False }

-- Descriptor de opciones de compilacion
options :: [OptDescr (Options -> Options)]
options = [ Option ['i'] ["input"]  (NoArg (\opts -> opts {optSrc = True})) "show input source code",
            Option ['a'] ["ast"]    (NoArg (\opts -> opts {optAST = True})) "show AST after escape analysis",
            Option ['p'] ["pretty"] (NoArg (\opts -> opts {optPPA = True})) "show pretty printed AST after escape analysis",
            Option ['f'] ["frags"]  (NoArg (\opts -> opts {optFgs = True})) "show generated IR fragments",
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
calculoEscapadas rawAST opts = 
                if (optEsc opts) then
                    case (stepperEscape rawAST) of
                        Left errEsc -> return $ Left errEsc
                        Right (exp, envs) -> do
                            printStepper envs
                            when (optAST opts) (printRawAst exp) 
                            when (optPPA opts) (printPrettyAst exp)
                            return (Right exp)
                else
                    case (simpleEscape rawAST) of
                        Left errEsc -> return $ Left errEsc
                        Right exp -> do 
                            when (optAST opts) (printRawAst exp) 
                            when (optPPA opts) (printPrettyAst exp)
                            return $ Right exp


--codgenStep :: Exp -> Bool -> GenSt [Frag]
--codgenStep e s = do
--    let sem = runLion e
--    when (isLeft sem) (error $ "Semantic core:"++ show (getLeft sem))
--    let (fs,temp,lbl) = getRight sem
--    when s (lift $ putStrLn $ foldr (\t ts -> renderFrag t ++ '\n':ts) "" fs)
--    setLabel lbl
--    setTemp temp
--    return fs
--
--canonStep' :: [Frag] -> GenSt ([Frag],[([Tree.Stm],Frame)])
--canonStep' xs = do
--    l <- getLabel
--    t <- getTemp
--    let (strs, procs) =  sepFrag xs
--    let (can, t', l') = canon t l procs
--    setLabel l'
--    setTemp t'
--    return (strs, can)
--
--canonStep :: [Frag] -> Bool -> GenSt ([Frag],[([Tree.Stm],Frame)])
--canonStep xs opt = do
--    (strs, procs) <- canonStep' xs
--    when opt ( -- Show Time!
--        lift $ putStrLn "Data Segment:" >>
--        mapM_ (putStrLn . renderFrag) strs >>
--        putStrLn "Code Segment:" >>
--        mapM_ (\(sts,fr) -> putStrLn $ renderPCan sts fr) procs)
--    return (strs,procs)

-- Printers para debug
printStepper envs = do
    putStrLn "**** stepper mode begin ****"
    mapM_ (putStrLn . show . toList) (reverse (e envs))
    putStrLn "**** stepper mode end ****\n"

printRawAst ast = do
    putStrLn "**** raw ast begin ****"
    putStrLn (show ast)
    putStrLn "**** raw ast end ****\n"

printPrettyAst ast = do
    putStrLn "**** pretty ast begin ****"
    putStrLn (renderExp ast)
    putStrLn "**** pretty ast end ****\n"

printFrags frags = do
    putStrLn "**** generated frags begin ****"
    putStrLn $ (concatMap show) frags --renderFrag) frags
    putStrLn "**** generated frags end ****\n"

printSourceCode src = do
    let srcLines = lines src
        maxWidth = length $ digs $ length srcLines
        padNumber n = take (maxWidth - (length $ digs n)) [' ', ' '..] ++ show n
    putStrLn "**** input source code begin ****"
    putStrLn $ intercalate "\n" $ zipWith (\l t -> padNumber l ++ "|" ++ t) [1..] $ lines src 
    putStrLn "**** input source code end ****\n"
   
digs :: Int -> [Int]
digs 0 = []
digs x = digs (x `div` 10) ++ [x `mod` 10]  


-- Helpers para desempaquetar either
fromLeft :: Either a b -> a
fromLeft (Left x) = x
fromLeft _ = error "called fromLeft with Right value"

fromRight :: Either a b -> b
fromRight (Right x) = x
fromRight _ = error "called fromRight with Left value"

-- override de Data.Either.isLeft 
-- no presente en la version de GHC del labdcc
isLeft (Left x) = True
isLeft _        = False

-- Handler para excepciones
printException :: SomeException -> IO Int
printException e = do putStrLn $ "tiger: " ++ show e 
                      return (-1)



---------------------------------------------
--                  MAIN                   --
---------------------------------------------
main = handle printException $ do
    -- Parseo de argumentos de linea de comandos,
    -- si falla muestro el mensaje de ayuda
    argv <- Env.getArgs
    let parsedArgv = parseCommand argv
    when (isLeft parsedArgv) (error $ fromLeft parsedArgv ++ "\n" ++
                                      usageInfo "Usage: tiger [OPTIONS] file" options)
    let (opts, file) = fromRight parsedArgv
    
    -- Leo archivo fuente
    sourceCode <- readFile file
    when (optSrc opts) $ printSourceCode sourceCode

    -- Parseo del archivo fuente
    let rawEAST = runParser expression () file sourceCode
    when (isLeft rawEAST) (error $ "error de parseo\n" ++ show (fromLeft rawEAST))
    
    -- Calculo de variables escapadas
    east <- calculoEscapadas (fromRight rawEAST) opts
    when (isLeft east) (error $ "error en el calculo de variables escapadas\n" ++ show (fromLeft east))
    
    -- Analisis semantico
    let seman = runLion $ fromRight east 
    when (isLeft seman) (error $ "error semantico\n" ++ show (fromLeft seman))
    
    let (frags, i1, i2) = fromRight seman
    when (optFgs opts) $ printFrags frags

   -- OBcodecanon <- evalStateT (do
   --         frags <- codgenStep (fromJust east) (optIr opts')
   --         canonStep frags (optCanon opts')) initState
   -- 
    putStrLn "finished"
    return 0
    

