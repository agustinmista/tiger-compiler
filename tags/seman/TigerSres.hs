module TigerSres where

import TigerTips
import TigerTemp

type FunEntry = (Unique, Label, [Tipo], Tipo, Bool)
type ValEntry = Tipo

data EnvEntry = 
    Var ValEntry | Func FunEntry
    deriving Show
