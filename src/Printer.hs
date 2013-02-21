module Printer where
  import Prelude hiding (print)
  import Text.PrettyPrint.HughesPJ
  
  import LP_Ast
  
  tPrint :: Int -> Type -> Doc
  tPrint _ (TFree (Global s))  =  text s
  tPrint _ (TFree _)           =  undefined
  tPrint p (Fun ty ty')        =  parensIf (p > 0) (sep [tPrint 0 ty <> text " ->", nest 2 (tPrint 0 ty')])
  
  iPrint :: Int -> Int -> ITerm -> Doc
  iPrint p ii (Ann c ty)       =  parensIf (p > 1) (cPrint 2 ii c <> text " :: " <> tPrint 0 ty)
  iPrint _ ii (Bound k)        =  text (vars !! (ii - k - 1))
  iPrint _ _  (Free (Global s))=  text s
  iPrint p ii (i :@: c)        =  parensIf (p > 2) (sep [iPrint 2 ii i, nest 2 (cPrint 3 ii c)])
  iPrint _ _  x                =  text ("[" ++ show x ++ "]")
  
  cPrint :: Int -> Int -> CTerm -> Doc
  cPrint p ii (Inf i)    = iPrint p ii i
  cPrint p ii (Lam c)    = parensIf (p > 0) (text "\\ " <> text (vars !! ii) <> text " -> " <> cPrint 0 (ii + 1) c)
  
  vars :: [String]
  vars = [ c : n | n <- "" : map show [1..], c <- "xyz" ++ ['a'..'w'] ]
  
  parensIf :: Bool -> Doc -> Doc
  parensIf True  = parens
  parensIf False = id
  
  print :: CTerm -> String
  print = render . cPrint 0 0
  
  printType :: Type -> String
  printType = render . tPrint 0

