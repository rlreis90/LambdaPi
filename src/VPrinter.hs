-- |Printer for run-time values.
module VPrinter where

  import Prelude hiding (print)
  import Text.PrettyPrint.HughesPJ
  
  import Ast
  
  parensIf :: Bool -> Doc -> Doc
  parensIf True  = parens
  parensIf False = id
  
  vars :: [String]
  vars = [ c : n | n <- "" : map show [1..], c <- ['a'..'z'] ]
  
  iPrint_ :: Int -> Int -> ITerm_ -> Doc
  
  iPrint_ p i expr =  
    case expr of
      Star_            ->  text "*"
      Nat_             ->  text "Nat"
  
      Ann_ c ty        ->  parensIf (p > 1) (cPrint_ 2 i c <> text " : " <> cPrint_ 0 i ty)
  
  --  Pi_ d (Inf_ (Pi_ d' r))
  --                   ->  parensIf (p > 0) (nestedForall_ (i + 2) [(i + 1, d'), (i, d)] r)
      
      Pi_ d r          ->  parensIf (p > 0) (sep [parens (text (vars !! i) <> text " : " <> cPrint_ 0 i d) <> text " ->", cPrint_ 0 (i + 1) r])
      
      Bound_ k         ->  text (vars !! (i - k - 1))
      Free_ (Global s) ->  text s
      term :$: c       ->  parensIf (p > 2) (sep [iPrint_ 2 i term, nest 2 (cPrint_ 3 i c)])
      

      Eq_ a x y        ->  iPrint_ p i (Free_ (Global "Eq") :$: a :$: x :$: y)
      EqElim_ a m mr x y eq
                                     ->  iPrint_ p i (Free_ (Global "eqElim") :$: a :$: m :$: mr :$: x :$: y :$: eq)
                                     
      NatElim_ m z s n ->  iPrint_ p i (Free_ (Global "natElim") :$: m :$: z :$: s :$: n)
      Vec_ a n         ->  iPrint_ p i (Free_ (Global "Vec") :$: a :$: n)
      VecElim_ a m mn mc n xs
                       ->  iPrint_ p i (Free_ (Global "vecElim") :$: a :$: m :$: mn :$: mc :$: n :$: xs)
                       
      Fin_ n           ->  iPrint_ p i (Free_ (Global "Fin") :$: n)
      FinElim_ m mz ms n f
                                     ->  iPrint_ p i (Free_ (Global "finElim") :$: m :$: mz :$: ms :$: n :$: f)
                                     
      x                ->  text ("[" ++ show x ++ "]")
  
  cPrint_ :: Int -> Int -> CTerm_ -> Doc
  cPrint_ p binder_depth expr =
    case expr of
      Inf_ inf   -> iPrint_ p binder_depth inf
      Lam_ c     -> parensIf (p > 0) 
                     (text "λ"
                     <> text (vars !! binder_depth)
                     <> text " -> "
                     <> cPrint_ 0 (binder_depth + 1) c)
      
      Zero_      -> fromNat_ 0 binder_depth Zero_     --  text "Zero"
      Succ_ n    -> fromNat_ 0 binder_depth (Succ_ n) --  iPrint_ p i (Free_ (Global "Succ") :$: n)
      Nil_ a     -> iPrint_ p binder_depth (Free_ (Global "Nil") :$: a)
      Cons_ a n x xs ->
                    iPrint_ p binder_depth (Free_ (Global "Cons") :$: a :$: n :$: x :$: xs)
      Refl_ a x  -> iPrint_ p binder_depth (Free_ (Global "Refl") :$: a :$: x)
      FZero_ n   -> iPrint_ p binder_depth (Free_ (Global "FZero") :$: n)
      FSucc_ n f -> iPrint_ p binder_depth (Free_ (Global "FSucc") :$: n :$: f)
  
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
  
  
  
  
  
  --- Experimental
  
  tyvars :: [String]
  tyvars = [ c : n | n <- "" : map show [1..], c <- ['A'..'Z'] ]
  
  
  
  getNext vars env =
    let candidate = head vars --will always work on infinite list xs
    in
    if free candidate env
    then candidate : env
    else getNext (tail vars) env
  
  
  free var env =
    case env of
      []   -> True
      x:xs -> (x /= var) && free var xs
  
  cAnnotate_ exp env =
  
   let loopVars ys = ys ++ fmap (++ "'") ys
       typeVars = loopVars $ fmap ((: [])) ['A'..'Z']
       natVars  = loopVars $ fmap ((: [])) ['m'..'l']
       otherVars = loopVars $ fmap ((: [])) ['x'..'v']
       collectionVars = fmap (++ "s") otherVars
       funVars = loopVars $ fmap ((: [])) ['f'..'j']
    in
    
    case exp of
      Inf_ Star_ -> getNext typeVars env 
      Inf_ Nat_  -> getNext natVars env
      Inf_ (Vec_ _ _) -> getNext collectionVars env
      Inf_ (Pi_ _ _)  -> getNext funVars env
      _          -> getNext otherVars env
      
  iAnnotate_ exp xs =
    case exp of
      Pi_ x e  -> let xs'  = cAnnotate_ x xs
                      xs'' = cAnnotate_ e xs'
                  in
                  (exp, xs'')
      Bound_ k  -> (Free_ (Global ( xs !! k )), xs)
      _         -> (exp, xs)
  