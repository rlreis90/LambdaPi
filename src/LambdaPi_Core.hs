
module LambdaPi_Core where
  import Control.Monad.Error
      
  import Operators
 
  import Ast
  import Data.Maybe (fromMaybe)  
             
  vapp :: Value -> Value -> Value  
  vapp (VLam f)      v  =  f v
  vapp (VNeutral n)  v  =  VNeutral (NApp n v)
  
  iEval :: ITerm -> (NameEnv Value,Env) -> Value
    
  iEval (Ann  e _)    d  =  cEval e d
  iEval (Free  x)     d  =  lookup x (fst d) |> fromMaybe (vfree x)
  iEval (Bound  ii)   d  =  snd d !! ii
  iEval (e1 :@: e2)   d  =  iEval e1 d `vapp` cEval e2 d
  
  cEval :: CTerm -> (NameEnv Value,Env) -> Value
  
  cEval (Inf  ii)   d    =  iEval ii d
  cEval (Lam  l)    env  =  VLam (\ x -> cEval l ((\ (e, d) -> (e, x : d)) env))
  
  cKind :: Context -> Type -> Kind -> Result ()
  cKind g (TFree x) Star
    =  case lookup x g of
         Just (HasKind Star)  ->  return ()
         Nothing              ->  throwError "unknown identifier"
  cKind g (Fun kk kk') Star
    =  do  cKind g kk   Star
           cKind g kk'  Star
 
  iType0 :: Context -> ITerm -> Result Type
  iType0 = iType 0
 
  iType :: Int -> Context -> ITerm -> Result Type
  iType ii g (Ann e ty)
    =  do  cKind g ty Star
           cType ii g e ty
           return ty
  iType ii g (Free x)
    =  case lookup x g of
         Just (HasType ty)  ->  return ty
         Nothing            ->  throwError "unknown identifier"
  iType ii g (e1 :@: e2)
    =  do  si <- iType ii g e1
           case si of
             Fun ty ty'  ->  do  cType ii g e2 ty
                                 return ty'
             _           ->  throwError "illegal application"
 
  cType :: Int -> Context -> CTerm -> Type -> Result ()
  cType ii g (Inf e) ty
    =  do  ty' <- iType ii g e
           unless ( ty == ty' ) (throwError "type mismatch")
           
  cType ii g (Lam e) (Fun ty ty')
    =  cType  (ii + 1) ((Local ii, HasType ty) : g)
              (cSubst 0 (Free (Local ii)) e) ty'
  cType ii g _ _
    =  throwError "type mismatch" 
        
  iSubst :: Int -> ITerm -> ITerm -> ITerm
  iSubst ii r (Ann e ty)   =  Ann (cSubst ii r e) ty
  iSubst ii r (Bound j)    =  if ii == j then r else Bound j
  iSubst _  _ (Free y)     =  Free y
  iSubst ii r (e1 :@: e2)  =  iSubst ii r e1 :@: cSubst ii r e2
  
  cSubst :: Int -> ITerm -> CTerm -> CTerm
  cSubst ii r (Inf e)      =  Inf (iSubst ii r e)
  cSubst ii r (Lam e)      =  Lam (cSubst (ii + 1) r e)
  
  quote0 :: Value -> CTerm
  quote0 = quote 0
 
  quote :: Int -> Value -> CTerm
  quote ii (VLam f)      =  Lam (quote (ii + 1) (f (vfree (Quote ii))))
  quote ii (VNeutral n)  =  Inf (neutralQuote ii n)
 
  neutralQuote :: Int -> Neutral -> ITerm
  neutralQuote ii (NFree x)   =  boundfree ii x
  neutralQuote ii (NApp n v)  =  neutralQuote ii n :@: quote ii v
  
  boundfree :: Int -> Name -> ITerm
  boundfree ii (Quote k)     =  Bound (ii - k - 1)
  boundfree _  x             =  Free x
  
 
    