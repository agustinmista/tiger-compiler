module TigerTips where

import Data.Text
import qualified Data.List as L

type Unique = Int

data RWO = RW | RO
    deriving (Show,Eq)

data Tipo = TUnit 
          | TNil 
          | TInt RWO 
          | TString 
          | TArray Tipo Unique 
          | TRecord [(Text, Tipo, Int)] Unique 
          | RefRecord Text 
          | TTipo Text
    deriving Eq


instance Show Tipo where
    show TUnit = "()"
    show TNil = "Nil"
    show (TInt _) = "int"
    show (TString) = "string"
    show (TArray t u) = "(array of " ++ show t ++ ")[uid=" ++ show u ++ "]"
    show (TRecord flds u) = "({" ++  (L.intercalate ", " (L.map (\(n,t,i) -> unpack n ++ " : " ++ show t) flds)) ++ "})[uid=" ++ show u ++ "]"
    show (RefRecord t) = "record ref"
    show (TTipo t) = unpack t

intiposIguales :: Tipo -> Tipo -> Bool -- optimizar?
intiposIguales (TRecord {}) TNil = True
intiposIguales TNil (TRecord {}) = True
intiposIguales (TRecord _ u1) (TRecord _ u2) = u1 == u2
intiposIguales (TArray _ u1) (TArray _ u2) = u1 == u2
intiposIguales (TInt _) (TInt _) = True
intiposIguales (TTipo _) _ = error "TTIPOOOOOOOOOO 1"
intiposIguales _ (TTipo _) = error "TTIPOOOOOOOOOO 2"
intiposIguales a b = a == b -- Eq

