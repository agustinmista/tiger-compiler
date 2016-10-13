{-# LANGUAGE TypeFamilies #-}
module TigerErrores where

import qualified Data.Text as T
import Prelude hiding (error)

strToErr :: String -> T.Text
strToErr = T.pack

class (Monad w) => Daemon w where
    data Error w :: *
    error :: Error w -> w a
    handle :: w a -> (Error w -> w a) -> w a
    internal :: T.Text -> Error w
    adder :: Error w -> T.Text -> Error w

addLer :: (Daemon w) => w a -> String -> w a
addLer c t = handle c (\e -> error $ adder e (T.pack t))

class (Daemon w) => NotFounder w where
    notfound :: T.Text -> Error w 
