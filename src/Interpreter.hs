
module Interpreter where
  import Control.Monad.Error
  import Data.List
  import Data.Char
  import Text.PrettyPrint.HughesPJ hiding (parens)
  import Text.ParserCombinators.Parsec hiding (parse, State)
  import System.Console.Haskeline hiding (catch)
  import qualified System.Console.Haskeline.History as HlHist
  
  import LambdaPi_Core
  import LP_Ast
  import Parser
  import Parser_LP
  import Printer
  import Printer_LP
  
  import Globals

  addHistory :: MonadException m => String -> m ()
  
  addHistory s = runInputT defaultSettings (putHistory (HlHist.addHistory s HlHist.emptyHistory))
  
  
  --  read-eval-print loop
  readevalprint :: Interpreter i c v t tinf inf -> State v inf -> IO ()
  
  readevalprint interpreter top_state@(interactive, _, _, _) =
  
    let rec interp state =
          let runcommand value =
                do
                  when interactive $ addHistory value
                  command  <- interpretCommand value
                  state' <- handleCommand interp state command
                  maybe (return ()) (rec interp) state'
          in
          do
            input <- do
                when interactive $ putStr (iprompt interp)
                getLine
                    
            if null input then rec interp state else runcommand input
    in
      do
        --  welcome
        when interactive $ putStrLn ("Interpreter for " ++ iname interpreter ++ ".\n" ++ "Type :? for help.")
        --  enter loop
        rec interpreter top_state
        
-- LINE 40 "Interpreter.lhs" #-}
  data Command = TypeOf String
               | Compile CompileForm
               | Browse
               | Quit
               | Help
               | Noop
 
  data CompileForm = CompileInteractive  String
                   | CompileFile         String
  
  data InteractiveCommand = Cmd [String] String (String -> Command) String
  
  commands :: [InteractiveCommand]
  commands
    =  [ Cmd [":type"]        "<expr>"  TypeOf         "print type of expression",
         Cmd [":browse"]      ""        (const Browse) "browse names in scope",
         Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                       "load program from file",
         Cmd [":quit"]        ""        (const Quit)   "exit interpreter",
         Cmd [":help",":?"]   ""        (const Help)   "display this list of commands" ]
  
  helpTxt :: [InteractiveCommand] -> String
  helpTxt ics
    =  "List of commands:  Any command may be abbreviated to :c where\n" ++
       "c is the first character in the full name.\n\n" ++
       "<expr>                  evaluate expression\n" ++
       "let <var> = <expr>      define variable\n" ++
       "assume <var> :: <expr>  assume variable\n\n"
       ++
       unlines (map (\ (Cmd cs a _ d) -> let  ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) cs))
                                         in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) ics)
  
  
  interpretCommand :: String -> IO Command
  interpretCommand text
    =  if ":" `isPrefixOf` text then
         do  let  (cmd,t')  =  break isSpace text
                  t         =  dropWhile isSpace t'
                  
             --  find matching commands
             let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
             case matching of
               [Cmd _ _ f _] 
                   ->  return (f t)
               []  ->  putStrLn ("Unknown command `" ++ cmd ++ "'. Type :? for help.")
                       >> return Noop
               _   ->  putStrLn ("Ambiguous command, could be " ++ intercalate ", " [ head cs | Cmd cs _ _ _ <- matching ] ++ ".")
                       >> return Noop
       else
         return (Compile $ CompileInteractive text)
  
  handleCommand :: Interpreter i c v t tinf inf -> State v inf -> Command -> IO (Maybe (State v inf))
  handleCommand interpreter state@(inter, _, ve, te) cmd
    =  case cmd of
         Quit   ->  when (not inter) (putStrLn "!@#$^&*") >> return Nothing
         Noop   ->  return (Just state)
         Help   ->  putStr (helpTxt commands) >> return (Just state)
         TypeOf e ->
                    do  x <- parseIO "<interactive>" (iiparse interpreter) e
                        t <- maybe (return Nothing) (iinfer interpreter ve te) x
                        maybe (return ()) (\u -> putStrLn (render (itprint interpreter u))) t
                        return (Just state)
         Browse ->  do  putStr (unlines [ s | Global s <- reverse (nub (map fst te)) ])
                        return (Just state)
         Compile c ->
                    do  state <- case c of
                                   CompileInteractive s -> compilePhrase interpreter state s
                                   CompileFile f        -> compileFile interpreter state f
                        return (Just state)
 
  compileFile :: Interpreter i c v t tinf inf -> State v inf -> String -> IO (State v inf)
  compileFile interpreter state@(inter, out, ve, te) f =
    do
      x <- readFile f
      stmts <- parseIO f (many (isparse interpreter)) x
      maybe (return state) (foldM (handleStmt interpreter) state) stmts
  
  compilePhrase :: Interpreter i c v t tinf inf -> State v inf -> String -> IO (State v inf)
  compilePhrase int state@(inter, out, ve, te) x =
    do
      x <- parseIO "<interactive>" (isparse int) x
      maybe (return state) (handleStmt int state) x
  
  data Interpreter i c v t tinf inf =
    I { iname :: String,
        iprompt :: String,
        iitype :: NameEnv v -> Ctx inf -> i -> Result t,
        iquote :: v -> c,
        ieval  :: NameEnv v -> i -> v,
        ihastype :: t -> inf,
        icprint :: c -> Doc,
        itprint :: t -> Doc,
        iiparse :: CharParser () i,
        isparse :: CharParser () (Stmt i tinf),
        iassume :: State v inf -> (String, tinf) -> IO (State v inf) }
 
  st :: Interpreter ITerm CTerm Value Type Info Info
  st = I { iname = "the simply typed lambda calculus",
           iprompt = "ST> ",
           iitype = \ _ c -> iType 0 c,
           iquote = quote0,
           ieval  = \ e x -> iEval x (e, []),
           ihastype = HasType,
           icprint = cPrint 0 0,
           itprint = tPrint 0,
           iiparse = parseITerm 0 [],
           isparse = parseStmt [],
           iassume = \ s (x, t) -> stassume s x t }
        where 
          stassume (inter, out, ve, te) x t 
              =     return (inter, out, ve, (Global x, t) : te)
  
          
  lp :: Interpreter ITerm_ CTerm_ Value_ Value_ CTerm_ Value_
  lp = I { iname = "lambda-Pi",
           iprompt = "LP> ",
           iitype = curry $ iType_ 0,
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
                  
                  
-- LINE 225 "Interpreter.lhs" #-}
  repLP :: Bool -> IO ()
  repLP b = readevalprint lp (b, [], lpve, lpte)
 
  repST :: Bool -> IO ()
  repST b = readevalprint st (b, [], [], [])
  
  iinfer :: Interpreter i c v a tinf inf  -> NameEnv v -> Ctx inf -> i -> IO (Maybe a)
  
  iinfer interpreter d g t =
    case iitype interpreter d g t of
      Left e  -> putStrLn e >> return Nothing
      Right v -> return (Just v)
 
  handleStmt :: Interpreter i c v t tinf inf -> State v inf -> Stmt i tinf -> IO (State v inf)
  
  handleStmt interpreter state@(inter, out, ve, te) stmt =
    do
      case stmt of
          Assume ass -> foldM (iassume interpreter) state ass 
          Let x e    -> checkEval x e
          Eval e     -> checkEval it e
          PutStrLn x -> putStrLn x >> return state
          Out f      -> return (inter, f, ve, te)
    where
      it = "it"
      --  checkEval :: String -> i -> IO (State v inf)
      checkEval i t =
        check interpreter state i t
          (\ (y, v) -> do
                         --  ugly, but we have limited space in the paper
                         --  usually, you'd want to have the bound identifier *and*
                         --  the result of evaluation
                         let outtext = render $ if i == it
                                                  then icprint interpreter (iquote interpreter v) <> text " :: " <> itprint interpreter y
                                                  else text i <> text " :: " <> itprint interpreter y
                         putStrLn outtext
                         unless (null out) (writeFile out (process outtext)))
                         
          (\ (y, v) -> (inter, "", (Global i, v) : ve, (Global i, ihastype interpreter y) : te))
 
  check :: Interpreter i c v t tinf inf -> State v inf -> String -> i  -> ((t, v) -> IO ()) -> ((t, v) -> State v inf) -> IO (State v inf)
  
  check interpreter state@(_, _, ve, te) _ t kp k =
      do
        --  typecheck and evaluate
        x <- iinfer interpreter ve te t
        case x of
          Nothing  ->
              --do  putStrLn "type error"
              return state
          Just y   ->
            do
              let v = ieval interpreter ve t
              kp (y, v)
              return (k (y, v))
  
  


  process :: String -> String
  process = unlines . map (\ x -> "< " ++ x) . lines
  