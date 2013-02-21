module Lens where

  modify :: Functor f => (a -> b) -> f a -> f b
  modify = fmap
  
  set :: Functor f => b -> f a -> f b
  set x = modify (const x)
  
  class Functor f => Copointed f where
    extract :: f a -> a
  
  get :: Copointed w => w a -> a
  get = extract

  lens :: (Copointed f) => f a -> (b -> f b, a)
  lens xs = ((\x -> set x xs), extract xs)
  
  tupply :: (a -> b, a) -> b
  tupply (f, a) = f a