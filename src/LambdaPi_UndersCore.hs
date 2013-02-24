module LambdaPi_UndersCore where

  import Control.Monad.Error
  import Ast
  import VPrinter
  
  typeMismatch inferred expected expr =
    "type mismatch:\n" ++ "type inferred:  " ++ cRender (quote0_ inferred)
               ++ "\n" ++ "type expected:  " ++ cRender (quote0_ expected)
               ++ "\n" ++ "for expression: " ++ iRender expr
               
  vapp_ :: Value_ -> Value_ -> Value_
  vapp_ (VLam_ f)      v  =  f v
  vapp_ (VNeutral_ n)  v  =  VNeutral_ (NApp_ n v)
 
  vfree_ :: Name -> Value_
  vfree_ n = VNeutral_ (NFree_ n)
 
  cEval_ :: CTerm_ -> (NameEnv Value_,Env_) -> Value_
  cEval_ (Inf_  ii)    d  =  iEval_ ii d
  cEval_ (Lam_  c)     d  =  VLam_ (\ x -> cEval_ c ((\ (e, d) -> (e, x : d)) d))

  cEval_ Zero_      d  = VZero_
  cEval_ (Succ_ k)  d  = VSucc_ (cEval_ k d)

  cEval_ (Nil_ a)          d  =  VNil_ (cEval_ a d)
  cEval_ (Cons_ a n x xs)  d  =  VCons_  (cEval_ a d) (cEval_ n d)
                                         (cEval_ x d) (cEval_ xs d)

  cEval_ (Refl_ a x)       d  =  VRefl_ (cEval_ a d) (cEval_ x d)

  cEval_ (FZero_ n)    d  =  VFZero_ (cEval_ n d)
  cEval_ (FSucc_ n f)  d  =  VFSucc_ (cEval_ n d) (cEval_ f d)

  iEval_ :: ITerm_ -> (NameEnv Value_,Env_) -> Value_
  iEval_ (Ann_  c _)       d  =  cEval_ c d

  iEval_ Star_           d  =  VStar_   
  iEval_ (Pi_ ty ty')    d  =  VPi_ (cEval_ ty d) (\ x -> cEval_ ty' (((\(e, d) -> (e,  (x : d))) d)))   

  iEval_ (Free_  x)      d  =  case lookup x (fst d) of Nothing ->  (vfree_ x); Just v -> v 
  iEval_ (Bound_  ii)    d  =  (snd d) !! ii
  iEval_ (i :$: c)       d  =  vapp_ (iEval_ i d) (cEval_ c d)

  iEval_ Nat_                  _  =  VNat_
  iEval_ (NatElim_ m mz ms n)  d 
    = 
      let  mzVal = cEval_ mz d
           msVal = cEval_ ms d
           rec nVal =
             case nVal of
               VZero_       ->  mzVal
               VSucc_ k     ->  msVal `vapp_` k `vapp_` rec k
               VNeutral_ n  ->  VNeutral_
                                (NNatElim_ (cEval_ m d) mzVal msVal n)
               _            ->  error "internal: eval natElim"
       in   rec (cEval_ n d)

  iEval_ (Vec_ a n)                 d  =  VVec_ (cEval_ a d) (cEval_ n d)

  iEval_ (VecElim_ a m mn mc n xs)  d  =
    let  mnVal  =  cEval_ mn d
         mcVal  =  cEval_ mc d
         rec nVal xsVal =
           case xsVal of
             VNil_ _          ->  mnVal
             VCons_ _ k x xs  ->  foldl vapp_ mcVal [k, x, xs, rec k xs]
             VNeutral_ n      ->  VNeutral_
                                  (NVecElim_  (cEval_ a d) (cEval_ m d)
                                              mnVal mcVal nVal n)
             _                ->  error "internal: eval vecElim"
    in   rec (cEval_ n d) (cEval_ xs d)

  iEval_ (Eq_ a x y)                d  =  VEq_ (cEval_ a d) (cEval_ x d) (cEval_ y d)
  iEval_ (EqElim_ a m mr x y eq)    d  =
    let  mrVal  =  cEval_ mr d
         rec eqVal =
           case eqVal of
             VRefl_ _ z -> mrVal `vapp_` z
             VNeutral_ n ->  
               VNeutral_ (NEqElim_  (cEval_ a d) (cEval_ m d) mrVal
                                    (cEval_ x d) (cEval_ y d) n)
             _ -> error "internal: eval eqElim"
    in   rec (cEval_ eq d)

  iEval_ (Fin_ n)                d  =  VFin_ (cEval_ n d)
  iEval_ (FinElim_ m mz ms n f)  d  =
    let  mzVal  =  cEval_ mz d
         msVal  =  cEval_ ms d
         rec fVal =
           case fVal of
             VFZero_ k        ->  mzVal `vapp_` k
             VFSucc_ k g      ->  foldl vapp_ msVal [k, g, rec g]
             VNeutral_ n'     ->  VNeutral_
                                  (NFinElim_  (cEval_ m d) (cEval_ mz d)
                                              (cEval_ ms d) (cEval_ n d) n')
             _                ->  error "internal: eval finElim"
    in   rec (cEval_ f d)


  -- Substitution
  
  iSubst_ :: Int -> ITerm_ -> ITerm_ -> ITerm_
  iSubst_ ii i'   (Ann_ c c')     =  Ann_ (cSubst_ ii i' c) (cSubst_ ii i' c')
  
  iSubst_ _  _  Star_           =  Star_  
  iSubst_ ii r  (Pi_ ty ty')    =  Pi_  (cSubst_ ii r ty) (cSubst_ (ii + 1) r ty')

  iSubst_ ii i' (Bound_ j)      =  if ii == j then i' else Bound_ j
  iSubst_ _  _  (Free_ y)       =  Free_ y
  iSubst_ ii i' (i :$: c)       =  iSubst_ ii i' i :$: cSubst_ ii i' c

  iSubst_ _  _  Nat_            =  Nat_
  iSubst_ ii r  (NatElim_ m mz ms _)
                                =  NatElim_ (cSubst_ ii r m)
                                            (cSubst_ ii r mz) (cSubst_ ii r ms)
                                            (cSubst_ ii r ms)

  iSubst_ ii r  (Vec_ a n)      =  Vec_ (cSubst_ ii r a) (cSubst_ ii r n)
  iSubst_ ii r  (VecElim_ a m mn mc n xs)
                                =  VecElim_ (cSubst_ ii r a) (cSubst_ ii r m)
                                            (cSubst_ ii r mn) (cSubst_ ii r mc)
                                            (cSubst_ ii r n) (cSubst_ ii r xs)



  iSubst_ ii r  (Eq_ a x y)     =  Eq_ (cSubst_ ii r a)
                                       (cSubst_ ii r x) (cSubst_ ii r y)
  iSubst_ ii r  (EqElim_ a m mr x y eq)
                                =  VecElim_ (cSubst_ ii r a) (cSubst_ ii r m)
                                            (cSubst_ ii r mr) (cSubst_ ii r x)
                                            (cSubst_ ii r y) (cSubst_ ii r eq)

  iSubst_ ii r  (Fin_ n)        =  Fin_ (cSubst_ ii r n)
  iSubst_ ii r  (FinElim_ m mz ms n f)
                                =  FinElim_ (cSubst_ ii r m)
                                            (cSubst_ ii r mz) (cSubst_ ii r ms)
                                            (cSubst_ ii r n) (cSubst_ ii r f)


  cSubst_ :: Int -> ITerm_ -> CTerm_ -> CTerm_
  
  cSubst_ ii i' (Inf_ i)      =  Inf_ (iSubst_ ii i' i)
  cSubst_ ii i' (Lam_ c)      =  Lam_ (cSubst_ (ii + 1) i' c)

  cSubst_ _  _  Zero_         =  Zero_
  cSubst_ ii r  (Succ_ n)     =  Succ_ (cSubst_ ii r n)

  cSubst_ ii r  (Nil_ a)      =  Nil_ (cSubst_ ii r a)
  cSubst_ ii r  (Cons_ a _ x xs)
                              =  Cons_ (cSubst_ ii r a) (cSubst_ ii r x)
                                       (cSubst_ ii r x) (cSubst_ ii r xs)

  cSubst_ ii r  (Refl_ a x)   =  Refl_ (cSubst_ ii r a) (cSubst_ ii r x)

  cSubst_ ii r  (FZero_ n)    =  FZero_ (cSubst_ ii r n)
  cSubst_ ii r  (FSucc_ n k)  =  FSucc_ (cSubst_ ii r n) (cSubst_ ii r k)

  quote_ :: Int -> Value_ -> CTerm_
  quote_ ii (VLam_ t)
    =     Lam_ (quote_ (ii + 1) (t (vfree_ (Quote ii))))

  quote_ _  VStar_        = Inf_ Star_ 
  quote_ ii (VPi_ v f)    = Inf_ (Pi_ (quote_ ii v) (quote_ (ii + 1) (f (vfree_ (Quote ii)))))

  quote_ ii (VNeutral_ n) = Inf_ (neutralQuote_ ii n)

  quote_ _  VNat_       =  Inf_ Nat_
  quote_ _  VZero_      =  Zero_
  quote_ ii (VSucc_ n)  =  Succ_ (quote_ ii n)

  quote_ ii (VVec_ a n)         =  Inf_ (Vec_ (quote_ ii a) (quote_ ii n))
  quote_ ii (VNil_ a)           =  Nil_ (quote_ ii a)
  quote_ ii (VCons_ a n x xs)   =  Cons_  (quote_ ii a) (quote_ ii n)
                                          (quote_ ii x) (quote_ ii xs)

  quote_ ii (VEq_ a x y)  =  Inf_ (Eq_ (quote_ ii a) (quote_ ii x) (quote_ ii y))
  quote_ ii (VRefl_ a x)  =  Refl_ (quote_ ii a) (quote_ ii x)

  quote_ ii (VFin_ n)           =  Inf_ (Fin_ (quote_ ii n))
  quote_ ii (VFZero_ n)         =  FZero_ (quote_ ii n)
  quote_ ii (VFSucc_ n f)       =  FSucc_  (quote_ ii n) (quote_ ii f)

  neutralQuote_ :: Int -> Neutral_ -> ITerm_
  neutralQuote_ ii (NFree_ v)
     =  boundfree_ ii v
  neutralQuote_ ii (NApp_ n v)
     =  neutralQuote_ ii n :$: quote_ ii v

  neutralQuote_ ii (NNatElim_ m z s n)
     =  NatElim_ (quote_ ii m) (quote_ ii z) (quote_ ii s) (Inf_ (neutralQuote_ ii n))

  neutralQuote_ ii (NVecElim_ a m mn mc n xs)
     =  VecElim_ (quote_ ii a) (quote_ ii m)
                 (quote_ ii mn) (quote_ ii mc)
                 (quote_ ii n) (Inf_ (neutralQuote_ ii xs))

  neutralQuote_ ii (NEqElim_ a m mr x y eq)
     =  EqElim_  (quote_ ii a) (quote_ ii m) (quote_ ii mr)
                 (quote_ ii x) (quote_ ii y)
                 (Inf_ (neutralQuote_ ii eq))

  neutralQuote_ ii (NFinElim_ m mz ms n f)
     =  FinElim_ (quote_ ii m)
                 (quote_ ii mz) (quote_ ii ms)
                 (quote_ ii n) (Inf_ (neutralQuote_ ii f))

  boundfree_ :: Int -> Name -> ITerm_
  boundfree_ ii (Quote k)     =  Bound_ ((ii - k - 1) `max` 0)
  boundfree_ _  x             =  Free_ x

  instance Show Value_ where
    show = show . quote0_

  type Type_     =  Value_  
  type Context_    =  [(Name, Type_)]
  
  quote0_ :: Value_ -> CTerm_
  quote0_ = quote_ 0 
 
  iType0_ :: (NameEnv Value_,Context_) -> ITerm_ -> Result Type_
  iType0_ = inferType_ 0

  inferType_ :: Int -> (NameEnv Value_,Context_) -> ITerm_ -> Result Type_
  inferType_ ii g (Ann_ e tyt )
    =     do  checkType_  ii g tyt VStar_
              let ty = cEval_ tyt (fst g, [])  
              checkType_ ii g e ty
              return ty
  inferType_ ii g Star_   
     =  return VStar_   
  inferType_ ii g (Pi_ tyt tyt')  
     =  do  checkType_ ii g tyt VStar_    
            let ty = cEval_ tyt (fst g, [])  
            checkType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty) : g))) g)  
                      (cSubst_ 0 (Free_ (Local ii)) tyt') VStar_  
            return VStar_   
  inferType_ ii g (Free_ x)
    =     case lookup x (snd g) of
            Just ty        ->  return ty
            Nothing        ->  throwError ("unknown identifier: " ++ iRender (Free_ x))
  inferType_ ii g (e1 :$: e2)
    =     do  si <- inferType_ ii g e1
              case si of
                VPi_  ty ty'  ->  do  checkType_ ii g e2 ty
                                      return ( ty' (cEval_ e2 (fst g, [])))
                _                  ->  throwError "illegal application"

  inferType_ _  _ Nat_                  =  return VStar_
  inferType_ ii g (NatElim_ m mz ms n)  =
    do  checkType_ ii g m (VPi_ VNat_ (const VStar_))
        let mVal  = cEval_ m (fst g, []) 
        checkType_ ii g mz (mVal `vapp_` VZero_)
        checkType_ ii g ms (VPi_ VNat_ (\ k -> VPi_ (mVal `vapp_` k) (\ _ -> mVal `vapp_` VSucc_ k)))
        checkType_ ii g n VNat_
        let nVal = cEval_ n (fst g, [])
        return (mVal `vapp_` nVal)

  inferType_ ii g (Vec_ a n) =
    do  checkType_ ii g a  VStar_
        checkType_ ii g n  VNat_
        return VStar_
        
  inferType_ ii g (VecElim_ a m mn mc n vs) =
    do  checkType_ ii g a VStar_
        let aVal = cEval_ a (fst g, [])
        checkType_ ii g m
          (  VPi_ VNat_ (\n -> VPi_ (VVec_ aVal n) (\ _ -> VStar_)))
        let mVal = cEval_ m (fst g, [])
        checkType_ ii g mn (foldl vapp_ mVal [VZero_, VNil_ aVal])
        checkType_ ii g mc
          (  VPi_ VNat_ (\ n -> 
             VPi_ aVal (\ y -> 
             VPi_ (VVec_ aVal n) (\ ys ->
             VPi_ (foldl vapp_ mVal [n, ys])
             (\ _ -> foldl vapp_ mVal [VSucc_ n, VCons_ aVal n y ys])))))
        checkType_ ii g n VNat_
        let nVal = cEval_ n (fst g, [])
        checkType_ ii g vs (VVec_ aVal nVal)
        let vsVal = cEval_ vs (fst g, [])
        return (foldl vapp_ mVal [nVal, vsVal])

  inferType_ i g (Eq_ a x y) = do
  
    checkType_ i g a VStar_
    let aVal = cEval_ a (fst g, [])
    checkType_ i g x aVal
    checkType_ i g y aVal
    return VStar_
        
  inferType_ i g (EqElim_ a m mr x y eq) =
    do  checkType_ i g a VStar_
        let aVal = cEval_ a (fst g, [])
        checkType_ i g m
          (VPi_ aVal (\ x ->
           VPi_ aVal (\ y ->
           VPi_ (VEq_ aVal x y) (const VStar_))))
        let mVal = cEval_ m (fst g, [])
        checkType_ i g mr
          (VPi_ aVal (\ x ->
           foldl vapp_ mVal [x, x]))
        checkType_ i g x aVal
        let xVal = cEval_ x (fst g, [])
        checkType_ i g y aVal
        let yVal = cEval_ y (fst g, [])
        checkType_ i g eq (VEq_ aVal xVal yVal)
        let eqVal = cEval_ eq (fst g, [])
        return (foldl vapp_ mVal [xVal, yVal])

  --- Checks whether in a given Context a Term has a certain Type.
  checkType_ :: Int -> (NameEnv Value_, Context_) -> CTerm_ -> Type_ -> Result ()
  
  checkType_ ii g (Inf_ expression) expected  =
    do 
      inferred <- inferType_ ii g expression
      unless ( quote0_ expected == quote0_ inferred )
         $ throwError (typeMismatch inferred expected expression)
                                
  checkType_ ii g (Lam_ e) ( VPi_ ty ty')
    =     checkType_  (ii + 1) (fst g, (Local ii, ty) : snd g)
                  (cSubst_ 0 (Free_ (Local ii)) e) ( ty' (vfree_ (Local ii)))

  checkType_ _  _ Zero_      VNat_  =  return ()
  checkType_ ii g (Succ_ k)  VNat_  =  checkType_ ii g k VNat_
     

  checkType_ ii g (Nil_ a) (VVec_ bVal VZero_) =
    do
      checkType_ ii g a VStar_
      let aVal = cEval_ a (fst g, []) 
      unless  (quote0_ aVal == quote0_ bVal)  (throwError "type mismatch")
  
  checkType_ ii g (Cons_ a n x xs) (VVec_ bVal (VSucc_ k)) =
    do
      checkType_ ii g a VStar_
      let aVal = cEval_ a (fst g, [])
      unless  (quote0_ aVal == quote0_ bVal) (throwError "type mismatch")
              
      checkType_ ii g n VNat_
      let nVal = cEval_ n (fst g, [])
      unless  (quote0_ nVal == quote0_ k)
              (throwError "number mismatch")
              
      checkType_ ii g x aVal
      checkType_ ii g xs (VVec_ bVal k)

  checkType_ ii g (Refl_ a z) (VEq_ bVal xVal yVal) =
    do
      checkType_ ii g a VStar_
      let aVal = cEval_ a (fst g, [])
      unless  (quote0_ aVal == quote0_ bVal)
              (throwError "type mismatch")
      checkType_ ii g z aVal
      let zVal = cEval_ z (fst g, [])
      unless  (quote0_ zVal == quote0_ xVal && quote0_ zVal == quote0_ yVal)
              (throwError "type mismatch")
  
  -- otherwise fail
  checkType_ _ _ _ _  =     throwError "type mismatch"