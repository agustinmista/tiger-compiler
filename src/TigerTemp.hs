{-# LANGUAGE TypeSynonymInstances,FlexibleInstances, TypeFamilies #-}
module TigerTemp where
import qualified Data.Text as T
import Control.Monad.State 

type Label = T.Text --nombres abstractos para variables locales
type Temp  = T.Text --nombres abstractos para direcciones de memoria estaticas

pack = T.pack
unpack = T.unpack

makeStringT :: Temp -> String
makeStringT = unpack

makeStringL :: Label -> String
makeStringL = unpack

detgenTemp :: Int -> Temp
detgenTemp i = pack ("T"++show i)

detgenLabel :: Int -> Label
detgenLabel i = pack ("L"++show i)

-- | Clase generadora de temps, y labels
class (Monad w) => TLGenerator w where
    newTemp :: w Temp    -- returns a new temporary from an infinite set of temps
    newLabel :: w Label  -- returns a new label from an infinite set of labels

-- instance (Monad w, TLGenerator w) => TLGenerator (StateT s w) where
--     newTemp = newTemp
--     newLabel = newLabel
        
