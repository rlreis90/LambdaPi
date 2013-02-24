module Operators where

  -- |Pipe operator. Pushes a value into a function, reversing function application syntax.
  (|>) :: a -> (a -> b) -> b
  x |> f = f x
  