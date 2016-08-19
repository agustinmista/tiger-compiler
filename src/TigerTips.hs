module TigerTips where

import Data.Text

type Unique = Int

data RWO = RW | RO
    deriving (Show,Eq)

data Tipo = TUnit | TNil | TInt RWO | TString | TArray Tipo Unique | TRecord [(Text, Tipo, Int)] Unique | RefRecord Text |  TTipo Text
    deriving (Show,Eq)

intiposIguales :: Tipo -> Tipo -> Bool -- optimizar?
intiposIguales (TRecord {}) TNil = True
intiposIguales TNil (TRecord {}) = True
intiposIguales (TRecord _ u1) (TRecord _ u2) = u1 == u2
intiposIguales (TArray _ u1) (TArray _ u2) = u1 == u2
intiposIguales (TInt _) (TInt _) = True
intiposIguales (TTipo _) _ =error "TTIPOOOOOOOOOO 1"
intiposIguales _ (TTipo _) =error "TTIPOOOOOOOOOO 2"
intiposIguales a b = a == b -- Eq

