{-# LANGUAGE TypeFamilies #-}
module TigerEnv where

import qualified Data.Map.Strict as M
-- import qualified Data.List as L

class (Monad w) => Environmental w where
    data Mapper w :: * -> * -> *
    lookupI ::(Ord a) => a -> Mapper w a d -> Maybe d -- Buscar
    insertI ::(Ord a) => a -> d -> Mapper w a d -> Mapper w a d
    intersecI :: (Ord a) =>  (d -> d -> d) -> Mapper w a d -> Mapper w a d -> Mapper w a d
    updateI :: (Ord a) => a -> d -> Mapper w a d -> Mapper w a d 
    emptyI :: Mapper w a d
    -- showMap :: (Show a, Show d) => Mapper w a d ->  w String 
            
class Stacker w where
    data Stack w :: * -> *
    push :: a -> Stack w a -> w (Stack w a)
    pop  :: Stack w a -> w (Stack w a)
    top  :: Stack w a -> w a

fromList :: (Ord a, Environmental m)=> [(a,k)] -> Mapper m a k
fromList = foldl (\env (k,d) -> insertI k d env) emptyI
