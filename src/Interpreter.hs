
module Interpreter where
  import Control.Monad.Error
  import Data.List
  import Data.Char
  import Text.PrettyPrint.HughesPJ hiding (parens)
  import Text.ParserCombinators.Parsec hiding (parse, State)
  
  import LambdaPi_Core
  import Ast
  import Parser
  import Printer
  
  import Prelude hiding (putStr,putStrLn)
  import Operators
  
  type InterpreterState v inf = (Bool, String, NameEnv v, Ctx inf)
    
  data Command = TypeOf String
               | Compile Form
               | Browse
               | Quit
               | Help
               | Noop
 
  data Form = Interactive  String
            | File         String
  
  data InteractiveCommand = Cmd [String] String (String -> Command) String
  
  commands :: [InteractiveCommand]
  commands
    =  [ Cmd [":type"]        "<expr>"  TypeOf            "print type of expression",
         Cmd [":browse"]      ""        (const Browse)    "browse names in scope",
         Cmd [":load"]        "<file>"  (Compile . File)  "load program from file",
         Cmd [":quit"]        ""        (const Quit)      "exit interpreter",
         Cmd [":help",":?"]   ""        (const Help)      "display this list of commands" ]
  
  helpTxt :: [InteractiveCommand] -> String
  helpTxt ics
    =  "List of commands:  Any command may be abbreviated to :c where\n" ++
       "c is the first character in the full name.\n\n" ++
       "<expr>                  evaluate expression\n" ++
       "let <var> = <expr>      define variable\n" ++
       "assume <var> :: <expr>  assume variable\n\n"
       ++
       unlines (map (\ (Cmd cs a _ d) -> let  ct = intercalate ", " (map (++ if null a then "" else ' ' : a) cs)
                                         in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) ics)
  
  
  interpretCommand :: String -> IO Command
  interpretCommand input
    =  if ":" `isPrefixOf` input then
         do
           let  (cmd,t')  =  break isSpace input
           let  t         =  dropWhile isSpace t'
                
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             [Cmd _ _ f _]  ->  return (f t)
             []             ->  do
                                  putStrLn ("Unknown command `" ++ cmd ++ "'. Type :? for help.")
                                  return Noop
             _              ->  do
                                  putStrLn ("Ambiguous command, could be " ++ intercalate ", " [ head cs | Cmd cs _ _ _ <- matching ] ++ ".")
                                  return Noop
       else
         return (Compile $ Interactive input)
  
  handleCommand :: Interpreter i c v t tinf inf ->
                   InterpreterState v inf ->
                   Command ->
                   IO (Maybe (InterpreterState v inf))
  
  handleCommand interp state@(inter, _, valueEnv, typeEnv) cmd =
    let done = return $ Just state
    in
    case cmd of
                          
       Noop     ->  done
       
       Quit     ->  putStrLn "!@#$^&*" |> unless inter -- haha
                      >> return Nothing
       
       Help     ->  putStr (helpTxt commands) >> done
                      
       TypeOf e ->  parseIO "<interactive>" (iiparse interp) e
                      >>= maybe (return Nothing) (iinfer interp valueEnv typeEnv)
                      >>= maybe (return ()) (putStrLn . render . itprint interp)
                      >> done
                     
       Browse    -> putStr (unlines [ symbol | Global symbol <- nub (fmap fst typeEnv) |> reverse ])
                      >> done

       Compile from -> 
                    case from of                     
                        Interactive command -> 
                           parseIO "<interactive>" (isparse interp) command
                             >>= maybe (return state) (handleStmt interp state)
                           
                        File path     ->                       
                          readFile path
                            >>= parseIO path (many $ isparse interp)
                            >>= maybe (return state) (foldM (handleStmt interp) state)
                            
                    |> fmap Just
   
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
        iassume :: InterpreterState v inf -> (String, tinf) -> IO (InterpreterState v inf) }
 
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
  
  
  iinfer :: Interpreter i c v a tinf inf  -> NameEnv v -> Ctx inf -> i -> IO (Maybe a)
  
  iinfer interpreter d g t =
    case iitype interpreter d g t of
      Left e  -> putStrLn e >> return Nothing
      Right v -> return (Just v)
 
  handleStmt :: Interpreter i c v t tinf inf -> InterpreterState v inf -> Stmt i tinf -> IO (InterpreterState v inf)
  
  handleStmt interpreter state@(inter, out, ve, te) stmt =
    case stmt of
        Assume xs -> foldM (iassume interpreter) state xs 
        Let x e    -> checkEval x e
        Eval e     -> checkEval it e
        PutStrLn x -> putStrLn x >> return state
        Out f      -> return (inter, f, ve, te)
    where
      it = "it"
      process = unlines . map (\ x -> "< " ++ x) . lines
      --  checkEval :: String -> i -> IO (State v inf)
      checkEval i t =
        check interpreter state i t
          (\ (y, v) -> do
               --  ugly, but we have limited space in the paper
               --  usually, you'd want to have the bound identifier *and*
               --  the result of evaluation
               let outtext = (if i == it
                              then icprint interpreter (iquote interpreter v) <> text " : " <> itprint interpreter y
                              else text i <> text " : " <> itprint interpreter y)
                             |> render
               putStrLn outtext
               writeFile out (process outtext) |> unless (null out))
                         
            (\ (y, v) -> (inter, "", (Global i, v) : ve, (Global i, ihastype interpreter y) : te))          
 
 
  check :: Interpreter i c v t tinf inf ->
           InterpreterState v inf ->
           String ->
           i ->
           ((t, v) -> IO ()) -> ((t, v) -> InterpreterState v inf)
           -> IO (InterpreterState v inf)
  
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
  
  

  
  