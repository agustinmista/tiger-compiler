
import TigerAbs
import TigerEscap
import qualified Data.Text as T

ejemplo1 :: Exp -- La variable a escapa.
ejemplo1 = LetExp
            [ VarDec (T.pack "a") Nothing Nothing (IntExp 1 (1,1)) (1,2)
            , FunctionDec
                    [ (T.pack "f1",[( T.pack "a1", Nothing, NameTy $ T.pack "int")], Just $ T.pack "int",VarExp (SimpleVar $ T.pack "a") (5,5),(5,2))]
            ]
            (IntExp 42 (8,1))
            (1,0)

ejemplo2 :: Exp -- La variable b no está definida.
ejemplo2 = LetExp
            [ VarDec (T.pack "a") Nothing Nothing (IntExp 1 (1,2)) (1,2)
            -- , VarDec "b" Nothing Nothing (IntExp 2 1) 2
            -- , VarDec "c" Nothing Nothing (IntExp 3 1) 3
            , FunctionDec
                    [ (T.pack "f1",[(T.pack "a1", Nothing, NameTy $ T.pack "int")], Just $ T.pack "int",VarExp (SimpleVar $ T.pack "b") (5,5),(5,6))]
            ]
            (IntExp 42 (8,1))
            (1,0)
