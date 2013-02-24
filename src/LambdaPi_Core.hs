
module LambdaPi_Core where
  import Control.Monad.Error
      
  import Operators
 
  import Ast
  import Data.Maybe (fromMaybe)  
             
  type Context = [(Name, Info)]
  
  vapp :: Value -> Value -> Value  
  vapp (VLam f)      v  =  f v
  vapp (VNeutral n)  v  =  VNeutral (NApp n v)
  
  iEval :: ITerm -> (NameEnv Value, Env) -> Value
  
  iEval expr =
     case expr of
       Ann  e _   ->  cEval e
       Free  x    ->  fromMaybe (vfree x) . lookup x . fst
       Bound  i   ->  at i . snd
       e1 :@: e2  ->  \d -> iEval e1 d `vapp` cEval e2 d

  cEval :: CTerm -> (NameEnv Value, Env) -> Value
  
  cEval (Inf e)  env  =  iEval e env
  cEval (Lam l)  env  =  VLam (\ x -> cEval l ((\ (e, d) -> (e, x : d)) env))
  
  cKind :: Context -> Type -> Kind -> Result ()
  cKind g (TFree x) Star
    =  case lookup x g of
         Just (HasKind Star)  ->  return ()
         Just (HasType _   )  ->  throwError "level mismatch"
         Nothing              ->  throwError "unknown identifier"
  cKind g (Fun k k') Star
    =  do  cKind g k   Star
           cKind g k'  Star
 
  iType0 :: Context -> ITerm -> Result Type
  iType0 = inferType 0

  inferType :: Int -> Context -> ITerm -> Result Type  
  -- does it infer Pi-types? 
  inferType i g expr =
    case expr of
      (Ann e ty) ->
        do
          cKind g ty Star
          checkType i g e ty
          return ty     
      (Free x)  ->
        case lookup x g of
          Just (HasKind _ )  ->  throwError "level mismatch" -- should never happen
          Just (HasType ty)  ->  return ty
          Nothing            ->  throwError "unknown identifier"
 
      (e1 :@: e2) -> 
        do
          si <- inferType i g e1
          case si of
            Fun ty ty'  ->  do
                              checkType i g e2 ty
                              return ty'
            _           ->  throwError "illegal application"
                  
      _           -> throwError "unhandled case" 
 
  checkType :: Int -> Context -> CTerm -> Type -> Result ()
  checkType i g (Inf e) ty
    =  do  ty' <- inferType i g e
           unless ( ty == ty' ) (throwError "type mismatch")
           
  checkType i g (Lam e) (Fun ty ty')
    =  checkType  (i + 1) ((Local i, HasType ty) : g)
              (cSubst 0 (Free (Local i)) e) ty'
  checkType _ _ _ _
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
  
 
    