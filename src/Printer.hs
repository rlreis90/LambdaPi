module Printer where
  import Prelude hiding (print)
  import Text.PrettyPrint.HughesPJ
  
  import Ast
  
  parensIf :: Bool -> Doc -> Doc
  parensIf True  = parens
  parensIf False = id
  
  vars :: [String]
  vars = [ c : n | n <- "" : map show [1..], c <- "xyz" ++ ['a'..'w'] ]
  
  -- TODO: Printing: Higher kinded types should have functional names
  -- for example: select name "f" when kind is "* -> *"
  
  -- TODO: Printing: Improve collision detection
  -- don't repeat variable names as in "x : (x : Nat) -> *"
  
  -- TODO: Printing: Capitalize Type variables
  -- instead of "x : *", have "A : *"

  -- TODO: Printing: Remove unreferenced variables from types.
  -- for example: in the type "(x : Nat) -> Type"
  -- if "x" does not occur in "Type", then the type should become: "Nat -> Type"
  
  
  tPrint :: Int -> Type -> Doc
  tPrint _ (TFree (Global s))  =  text s
  tPrint _ (TFree _)           =  undefined
  tPrint p (Fun ty ty')        =  parensIf (p > 0) (sep [tPrint 0 ty <> text " ->", nest 2 (tPrint 0 ty')])
  
  iPrint :: Int -> Int -> ITerm -> Doc
  iPrint p i (Ann c ty)         =  parensIf (p > 1) (cPrint 2 i c <> text " : " <> tPrint 0 ty)
  iPrint _ i (Bound k)          =  text (vars !! (i - k - 1))
  iPrint _ _  (Free (Global s)) =  text s
  iPrint p i (inf :@: c)        =  parensIf (p > 2) (sep [iPrint 2 i inf, nest 2 (cPrint 3 i c)])
  iPrint _ _  x                 =  text ("[" ++ show x ++ "]")
  
  cPrint :: Int -> Int -> CTerm -> Doc
  cPrint p i (Inf inf)    = iPrint p i inf
  cPrint p i (Lam c)      = parensIf (p > 0) (text "\\ " <> text (vars !! i) <> text " -> " <> cPrint 0 (i + 1) c)
  
  
  print :: CTerm -> String
  print = render . cPrint 0 0
  
  printType :: Type -> String
  printType = render . tPrint 0