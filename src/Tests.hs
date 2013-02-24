
module Tests where
  import Ast
  import LambdaPi_Core
  
  id' :: CTerm
  id'      =  Lam (Inf (Bound 0))
  const' :: CTerm
  const'   =  Lam (Lam (Inf (Bound 1)))
 
  tfree :: String -> Type
  tfree a  =  TFree (Global a)
  free :: String -> CTerm
  free x   =  Inf (Free (Global x))
    
  --test data
  
  term1 :: ITerm
  term1    =  Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y"

  term2 :: ITerm
  term2    =  Ann const' (Fun  (Fun (tfree "b") (tfree "b"))
                               (Fun  (tfree "a")
                                     (Fun (tfree "b") (tfree "b"))))
              :@: id' :@: free "y" 
 
  env1 :: [(Name, Info)]
  env1  =  [(Global "y", HasType (tfree "a")),
               (Global "a", HasKind Star)]
               
  env2 :: [(Name, Info)]
  env2  = (Global "b", HasKind Star) : env1
  
  test_eval1 :: CTerm
  test_eval1=  quote0 (iEval term1 ([],[]))
   {-  \eval{test_eval1}  -}
 
  test_eval2 :: CTerm
  test_eval2=  quote0 (iEval term2 ([],[]))
   {-  \eval{test_eval2}  -}
 
  test_type1 :: Result Type
  test_type1=  iType0 env1 term1
   {-  \eval{test_type1}  -}
 
  test_type2 :: Result Type
  test_type2=  iType0 env2 term2
   {-  \eval{test_type2}  -}