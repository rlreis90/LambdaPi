module REPL where

  import Control.Monad.Error
  import Ast
  import LambdaPi_Core
  import Interpreter
  import Globals
  
  import Parser_LP
  import Printer_LP
  
  import Operators
  
  --  read-eval-print loop
  readevalprint :: Interpreter i c v t tinf inf -> InterpreterState v inf -> IO ()
  
  readevalprint interpreter top_state@(interactive, _, _, _) =
  
    let rec interp state =
          let runcommand value = do
              addHistory value |> when interactive
              interpretCommand value
                >>= handleCommand interp state
                >>= maybe (return ()) (rec interp)
          in
          do
            input <- do
                when interactive $ putStr (iprompt interp)
                getLine
                    
            if null input then rec interp state else runcommand input
    in
      do
        --  welcome
        putStrLn ("Interpreter for " ++ iname interpreter ++ ".\n" ++ "Type :? for help.")
          |> when interactive
        --  enter loop
        rec interpreter top_state
    
                  
  lambdaPi :: Bool -> IO ()
  lambdaPi b = readevalprint lp (b, [], lpve, lambdaPiTypeEnv)
 
  repST :: Bool -> IO ()
  repST b = readevalprint st (b, [], [], [])
  
          
  lp :: Interpreter ITerm_ CTerm_ Value_ Value_ CTerm_ Value_
  lp = I { iname = "lambda-Pi",
           iprompt = "LP> ",
           iitype = curry $ inferType_ 0,
           iquote = quote0_,
           ieval = \ e x -> iEval_ x (e, []),
           ihastype = id,
           icprint = cPrint_ 0 0,
           itprint = cPrint_ 0 0 . quote0_,
           iiparse = parseITerm_ 0 [],
           isparse = parseStmt_ [],
           iassume = \ s (x, t) -> lpassume s x t }
 
        where 
          lpassume state@(inter, out, ve, te) x t =
            check lp state x (Ann_ t (Inf_ Star_))
                  (\ (_, _) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint_ 0 0 (quote0_ v))))
                  (\ (_, v) -> (inter, out, ve, (Global x, v) : te))