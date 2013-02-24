module Printer where
  import Prelude hiding (print)
  import Text.PrettyPrint.HughesPJ
  
  import Ast
  
  tPrint :: Int -> Type -> Doc
  tPrint _ (TFree (Global s))  =  text s
  tPrint _ (TFree _)           =  undefined
  tPrint p (Fun ty ty')        =  parensIf (p > 0) (sep [tPrint 0 ty <> text " ->", nest 2 (tPrint 0 ty')])
  
  iPrint :: Int -> Int -> ITerm -> Doc
  iPrint p ii (Ann c ty)       =  parensIf (p > 1) (cPrint 2 ii c <> text " : " <> tPrint 0 ty)
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


  iPrint_ :: Int -> Int -> ITerm_ -> Doc
  iPrint_ p ii (Ann_ c ty)       =  parensIf (p > 1) (cPrint_ 2 ii c <> text " :: " <> cPrint_ 0 ii ty)
  iPrint_ p ii Star_             =  text "*"
  iPrint_ p ii (Pi_ d (Inf_ (Pi_ d' r)))
                                 =  parensIf (p > 0) (nestedForall_ (ii + 2) [(ii + 1, d'), (ii, d)] r)
  iPrint_ p ii (Pi_ d r)         =  parensIf (p > 0) (sep [text "forall " <> text (vars !! ii) <> text " :: " <> cPrint_ 0 ii d <> text " .", cPrint_ 0 (ii + 1) r])
  iPrint_ p ii (Bound_ k)        =  text (vars !! (ii - k - 1))
  iPrint_ p ii (Free_ (Global s))=  text s
  iPrint_ p ii (i :$: c)         =  parensIf (p > 2) (sep [iPrint_ 2 ii i, nest 2 (cPrint_ 3 ii c)])
  iPrint_ p ii Nat_              =  text "Nat"
  iPrint_ p ii (NatElim_ m z s n)=  iPrint_ p ii (Free_ (Global "natElim") :$: m :$: z :$: s :$: n)
  iPrint_ p ii (Vec_ a n)        =  iPrint_ p ii (Free_ (Global "Vec") :$: a :$: n)
  iPrint_ p ii (VecElim_ a m mn mc n xs)
                                 =  iPrint_ p ii (Free_ (Global "vecElim") :$: a :$: m :$: mn :$: mc :$: n :$: xs)
  iPrint_ p ii (Eq_ a x y)       =  iPrint_ p ii (Free_ (Global "Eq") :$: a :$: x :$: y)
  iPrint_ p ii (EqElim_ a m mr x y eq)
                                 =  iPrint_ p ii (Free_ (Global "eqElim") :$: a :$: m :$: mr :$: x :$: y :$: eq)
  iPrint_ p ii (Fin_ n)          =  iPrint_ p ii (Free_ (Global "Fin") :$: n)
  iPrint_ p ii (FinElim_ m mz ms n f)
                                 =  iPrint_ p ii (Free_ (Global "finElim") :$: m :$: mz :$: ms :$: n :$: f)
  iPrint_ p ii x                 =  text ("[" ++ show x ++ "]")
  
  cPrint_ :: Int -> Int -> CTerm_ -> Doc
  cPrint_ p ii (Inf_ i)    = iPrint_ p ii i
  cPrint_ p ii (Lam_ c)    = parensIf (p > 0) (text "\\ " <> text (vars !! ii) <> text " -> " <> cPrint_ 0 (ii + 1) c)
  cPrint_ p ii Zero_       = fromNat_ 0 ii Zero_     --  text "Zero"
  cPrint_ p ii (Succ_ n)   = fromNat_ 0 ii (Succ_ n) --  iPrint_ p ii (Free_ (Global "Succ") :$: n)
  cPrint_ p ii (Nil_ a)    = iPrint_ p ii (Free_ (Global "Nil") :$: a)
  cPrint_ p ii (Cons_ a n x xs) =
                             iPrint_ p ii (Free_ (Global "Cons") :$: a :$: n :$: x :$: xs)
  cPrint_ p ii (Refl_ a x) = iPrint_ p ii (Free_ (Global "Refl") :$: a :$: x)
  cPrint_ p ii (FZero_ n)  = iPrint_ p ii (Free_ (Global "FZero") :$: n)
  cPrint_ p ii (FSucc_ n f)= iPrint_ p ii (Free_ (Global "FSucc") :$: n :$: f)
  
  fromNat_ :: Int -> Int -> CTerm_ -> Doc
  fromNat_ n ii Zero_ = int n
  fromNat_ n ii (Succ_ k) = fromNat_ (n + 1) ii k
  fromNat_ n ii t = parensIf True (int n <> text " + " <> cPrint_ 0 ii t)
  
  nestedForall_ :: Int -> [(Int, CTerm_)] -> CTerm_ -> Doc
  nestedForall_ ii ds (Inf_ (Pi_ d r)) = nestedForall_ (ii + 1) ((ii, d) : ds) r
  nestedForall_ ii ds x                = sep [text "forall " <> sep [parensIf True (text (vars !! n) <> text " :: " <> cPrint_ 0 n d) | (n,d) <- reverse ds] <> text " .", cPrint_ 0 ii x]
  
  cRender :: CTerm_ -> String
  cRender = render . cPrint_ 0 0
  
  iRender :: ITerm_ -> String
  iRender = render . iPrint_ 0 0