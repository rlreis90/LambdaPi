module Printer where
  import Prelude hiding (print)
  import Text.PrettyPrint.HughesPJ
  
  import Ast
  
  -- TODO: Better variable name generation.
  -- for example: select name "f" when kind is "* -> *"
  -- and do not repeat variable names such as in "f : (f : Nat) -> Type"

  -- TODO: Remove unreferenced variables from types.
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
  cPrint p i (Lam c)    = parensIf (p > 0) (text "\\ " <> text (vars !! i) <> text " -> " <> cPrint 0 (i + 1) c)
  
  vars :: [String]
  vars = [ c : n | n <- "" : map show [1..], c <- "xyz" ++ ['a'..'w'] ]
  
  parensIf :: Bool -> Doc -> Doc
  parensIf True  = parens
  parensIf False = id
  
  print :: CTerm -> String
  print = render . cPrint 0 0
  
  printType :: Type -> String
  printType = render . tPrint 0


  iPrint_ :: Int -> Int -> ITerm_ -> Doc
  iPrint_ _ _  Star_             =  text "Type"
  iPrint_ _ _  Nat_              =  text "Nat"
  iPrint_ p i (Ann_ c ty)        =  parensIf (p > 1) (cPrint_ 2 i c <> text " : " <> cPrint_ 0 i ty)
  iPrint_ p i (Pi_ d (Inf_ (Pi_ d' r)))
                                 =  parensIf (p > 0) (nestedForall_ (i + 2) [(i + 1, d'), (i, d)] r)
  iPrint_ p i (Pi_ d r)          =  parensIf (p > 0) (sep [parens (text (vars !! i) <> text " : " <> cPrint_ 0 i d) <> text " ->", cPrint_ 0 (i + 1) r])
  iPrint_ _ i (Bound_ k)         =  text (vars !! (i - k - 1))
  iPrint_ _ _  (Free_ (Global s))=  text s
  iPrint_ p i (inf :$: c)        =  parensIf (p > 2) (sep [iPrint_ 2 i inf, nest 2 (cPrint_ 3 i c)])
  iPrint_ p i (NatElim_ m z s n) =  iPrint_ p i (Free_ (Global "natElim") :$: m :$: z :$: s :$: n)
  iPrint_ p i (Vec_ a n)         =  iPrint_ p i (Free_ (Global "Vec") :$: a :$: n)
  iPrint_ p i (VecElim_ a m mn mc n xs)
                                 =  iPrint_ p i (Free_ (Global "vecElim") :$: a :$: m :$: mn :$: mc :$: n :$: xs)
  iPrint_ p i (Eq_ a x y)        =  iPrint_ p i (Free_ (Global "Eq") :$: a :$: x :$: y)
  iPrint_ p i (EqElim_ a m mr x y eq)
                                 =  iPrint_ p i (Free_ (Global "eqElim") :$: a :$: m :$: mr :$: x :$: y :$: eq)
  iPrint_ p i (Fin_ n)           =  iPrint_ p i (Free_ (Global "Fin") :$: n)
  iPrint_ p i (FinElim_ m mz ms n f)
                                 =  iPrint_ p i (Free_ (Global "finElim") :$: m :$: mz :$: ms :$: n :$: f)
                                 
  iPrint_ _ _  x                 =  text ("[" ++ show x ++ "]")
  
  cPrint_ :: Int -> Int -> CTerm_ -> Doc
  cPrint_ p i (Inf_ inf)  = iPrint_ p i inf
  cPrint_ p i (Lam_ c)    = parensIf (p > 0) (text "λ" <> text (vars !! i) <> text " -> " <> cPrint_ 0 (i + 1) c)
  cPrint_ _ i Zero_       = fromNat_ 0 i Zero_     --  text "Zero"
  cPrint_ _ i (Succ_ n)   = fromNat_ 0 i (Succ_ n) --  iPrint_ p i (Free_ (Global "Succ") :$: n)
  cPrint_ p i (Nil_ a)    = iPrint_ p i (Free_ (Global "Nil") :$: a)
  cPrint_ p i (Cons_ a n x xs) =
                            iPrint_ p i (Free_ (Global "Cons") :$: a :$: n :$: x :$: xs)
  cPrint_ p i (Refl_ a x) = iPrint_ p i (Free_ (Global "Refl") :$: a :$: x)
  cPrint_ p i (FZero_ n)  = iPrint_ p i (Free_ (Global "FZero") :$: n)
  cPrint_ p i (FSucc_ n f)= iPrint_ p i (Free_ (Global "FSucc") :$: n :$: f)
  
  fromNat_ :: Int -> Int -> CTerm_ -> Doc
  fromNat_ n _  Zero_ = int n
  fromNat_ n i (Succ_ k) = fromNat_ (n + 1) i k
  fromNat_ n i t = parensIf True (int n <> text " + " <> cPrint_ 0 i t)
  
  nestedForall_ :: Int -> [(Int, CTerm_)] -> CTerm_ -> Doc
  nestedForall_ i ds (Inf_ (Pi_ d r)) = nestedForall_ (i + 1) ((i, d) : ds) r
  nestedForall_ i ds x                = sep [sep [parens (text (vars !! n)
                                                   <> text " : "
                                                   <> cPrint_ 0 n d) | (n,d) <- reverse ds]
                                              <> text " ->"
                                            , cPrint_ 0 i x]
  
  cRender :: CTerm_ -> String
  cRender = render . cPrint_ 0 0
  
  iRender :: ITerm_ -> String
  iRender = render . iPrint_ 0 0