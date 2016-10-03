module TigerSres where

import TigerTips
import TigerTemp
import TigerTrans
import TigerFrame

type FunEntry = (Level, Label, [Tipo], Tipo, Bool)
type ValEntry = (Tipo, Access, Int)

data EnvEntry = 
    Var ValEntry | Func FunEntry
    deriving Show
