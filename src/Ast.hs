
module Ast where    
    
  data Stmt i tinf = Let String i           --  let x = t
                   | Assume [(String,tinf)] --  assume x :: t, assume x :: *
                   | Eval i
                   | PutStrLn String        --  lhs2TeX hacking, allow to print "magic" string
                   | Out String             --  more lhs2TeX hacking, allow to print to files
                   deriving (Show)
    
  type Result a = Either String a
  type NameEnv v = [(Name, v)]
  type Ctx inf = [(Name, inf)]
  
  data ITerm
     =  Ann    CTerm Type
     |  Bound  Int
     |  Free   Name
     |  ITerm :@: CTerm
    deriving (Show, Eq)
  
  data CTerm
     =  Inf  ITerm 
     |  Lam  CTerm
    deriving (Show, Eq)
 
  data Name
     =  Global  String
     |  Local   Int
     |  Quote   Int
    deriving (Show, Eq)
        
  data Type
     =  TFree  Name
     |  Fun    Type Type
    deriving (Show, Eq)
        
  data Value
     =  VLam      (Value -> Value)
     |  VNeutral  Neutral
         
  data Neutral
     =  NFree  Name
     |  NApp   Neutral Value
         
  vfree :: Name -> Value
  vfree n = VNeutral (NFree n)
  
  data Kind = Star
    deriving (Show)
 
  data Info
     =  HasKind  Kind
     |  HasType  Type 
    deriving (Show)
 
  type Context = [(Name, Info)]
  
  type Env = [Value]
  
  data CTerm_
     =  Inf_  ITerm_
     |  Lam_  CTerm_
         
     |  Zero_
     |  Succ_ CTerm_
         
     |  Nil_ CTerm_
     |  Cons_ CTerm_ CTerm_ CTerm_ CTerm_
     |  Refl_ CTerm_ CTerm_
     |  FZero_ CTerm_
     |  FSucc_ CTerm_ CTerm_
         
    deriving (Show, Eq)
        
  data ITerm_
     =  Ann_ CTerm_ CTerm_
     |  Star_
     |  Pi_ CTerm_ CTerm_
     |  Bound_  Int
     |  Free_  Name
     |  ITerm_ :$: CTerm_
         
     |  Nat_
     |  NatElim_ CTerm_ CTerm_ CTerm_ CTerm_
         
     |  Vec_ CTerm_ CTerm_
     |  VecElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
     
     |  Eq_ CTerm_ CTerm_ CTerm_
     |  EqElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
         
     |  Fin_ CTerm_
     |  FinElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
         
    deriving (Show, Eq)
        

  type Env_ = [Value_]
  
  data Value_
     =  VLam_  (Value_ -> Value_)
     |  VStar_
     |  VPi_ Value_ (Value_ -> Value_)
     |  VNeutral_ Neutral_
         
    |  VNat_
    |  VZero_
    |  VSucc_ Value_
        
    |  VNil_ Value_
    |  VCons_ Value_ Value_ Value_ Value_
    |  VVec_ Value_ Value_
        
    |  VEq_ Value_ Value_ Value_
    |  VRefl_ Value_ Value_
        
    |  VFZero_ Value_
    |  VFSucc_ Value_ Value_
    |  VFin_ Value_
        
  data Neutral_
     =  NFree_  Name
     |  NApp_  Neutral_ Value_
     |  NNatElim_ Value_ Value_ Value_ Neutral_

     |  NVecElim_ Value_ Value_ Value_ Value_ Value_ Neutral_

     |  NEqElim_ Value_ Value_ Value_ Value_ Value_ Neutral_
     |  NFinElim_ Value_ Value_ Value_ Value_ Neutral_
     