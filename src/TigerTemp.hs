{-# LANGUAGE TypeSynonymInstances,FlexibleInstances, TypeFamilies #-}
module TigerTemp where
import qualified Data.Text as T
import Control.Monad.State 

type Label = T.Text
type Temp  = T.Text

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
    newTemp :: w Temp
    newLabel :: w Label

-- instance (Monad w, TLGenerator w) => TLGenerator (StateT s w) where
--     newTemp = newTemp
--     newLabel = newLabel
        
