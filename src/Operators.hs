module Operators where

  import Prelude hiding (putStr,putStrLn)
  import qualified Data.ByteString.Char8 as Utf
  import Data.ByteString.UTF8 (fromString)
  
  -- |Pipe operator. Pushes a value into a function, reversing function application syntax.
  (|>) :: a -> (a -> b) -> b
  x |> f = f x
  
  putStr = Utf.putStr . fromString
  
  putStrLn = Utf.putStrLn . fromString