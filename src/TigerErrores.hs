{-# LANGUAGE TypeFamilies #-}
module TigerErrores where

import qualified Data.Text as T

class (Monad w) => Deamon w where
    data Error w :: *
    error :: Error w -> w a
    handle :: w a -> (Error w -> w a) -> w a
    internal :: T.Text -> Error w
    adder :: Error w -> T.Text -> Error w

class (Deamon w) => NotFounder w where
    notfound :: T.Text -> Error w 

