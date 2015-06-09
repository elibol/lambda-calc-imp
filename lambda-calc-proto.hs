{-# LANGUAGE QuasiQuotes #-}

import Data.Map (Map)
import Data.Monoid
import qualified Data.Map as Map
import Data.SExp

----------------------------------------
-- Expressions
----------------------------------------

data Exp =
    Var String            -- x
  | Lambda String Exp     -- (lambda (x) e)
  | App Exp Exp           -- (e1 e2)
  | StringLit String      -- "foo"
  | Concat Exp Exp        -- (concat e1 e2)
  | Output Exp            -- (output e)
  | UnitLit               -- unit
  deriving (Eq, Ord, Show)

----------------------------------------
-- Values
----------------------------------------

data Val =
    Closure String Exp Env
  | StringVal String
  | UnitVal
  deriving (Eq, Ord, Show)

-- The variable environment
-- mapping variables to values
type Env = Map String Val

----------------------------------------
-- Monad
----------------------------------------

-- A monad which supports failure and output effects
data MaybeWriter w a = MaybeWriter (Maybe a, w)

mwReturn :: (Monoid w) => a -> MaybeWriter w a
mwReturn a = MaybeWriter (Just a, mempty)

mwBind :: (Monoid w) => MaybeWriter w a -> (a -> MaybeWriter w b) -> MaybeWriter w b
mwBind (MaybeWriter (Just x, v)) f = let (MaybeWriter (y, v')) = f x in (MaybeWriter (y, v `mappend` v'))
mwBind (MaybeWriter (Nothing, v)) f = (MaybeWriter (Nothing, v))

mwFailure :: (Monoid w) => MaybeWriter w a
mwFailure = MaybeWriter (Nothing, mempty)

mwOutput :: (Monoid w) => w -> MaybeWriter w ()
mwOutput w = MaybeWriter(Just (), w)

instance (Monoid w) => Monad (MaybeWriter w) where
  return = mwReturn
  (>>=) = mwBind
  
  -- Note that this is an implementation of the Monad instance.
  fail _ = mwFailure

----------------------------------------
-- Evaluator
----------------------------------------
  
-- (evalM e env) evaluates 'e' in the environment 'env' to a final value inside
-- the MaybeWriter monad.  The monoid which the monad manipulates is a String,
-- which is the output that accumulates during evaluation.
evalM :: Exp -> Env -> MaybeWriter String Val
evalM e env = 
  case e of 
    
    UnitLit -> return UnitVal
    
    StringLit s -> return (StringVal s)
    
    Lambda x e -> return (Closure x e env)
    
    Var x -> case (Map.lookup x env) of 
      (Just v) -> return v
      Nothing -> mwFailure
      
    App e1 e2 -> do
      (Closure x e env) <- evalM e1 env
      v2 <- evalM e2 env
      v  <- evalM e (Map.insert x v2 env)
      return v
      
    Concat e1 e2 -> do
      StringVal s1 <- evalM e1 env
      StringVal s2 <- evalM e2 env
      return $ StringVal $ (++) s1 s2
      
    Output e -> do
      StringVal s <- evalM e env
      u <- mwOutput s
      return UnitVal

-- (eval e env) evaluates 'e' in the environment 'env' to a final pure result.
--
-- The result is either Nothing, indicating failure, or Just (v, out)
-- indicating a result value 'v' with global output 'out'.
eval :: Exp -> Env -> Maybe (Val, String)
eval e env = case (evalM e env) of
    MaybeWriter (Just v, out) -> Just (v, out)
    MaybeWriter (Nothing, out) -> Nothing

----------------------------------------
-- Expressions
----------------------------------------

e1 :: Exp
e1 = parse [sexp|

((lambda (z)
  (output " world"))
 (output "hello"))

|]

e2 :: Exp
e2 = parse [sexp| 

((lambda (fconcat)
 (output ((((lambda (x) x) 
            fconcat) 
           "hello") 
          " world")))
 (lambda (x) 
  (lambda (y) 
   ((lambda (z) 
     (concat x y))
    unit))))

|]

----------------------------------------
-- TESTS
----------------------------------------

type Output = Maybe (Val, String)
tests :: [(Exp, Output)]
tests = [
  -- var error
  (parse [sexp| x |], Nothing)
  -- string
  , (parse [sexp| "hi" |], Just (StringVal "hi", ""))
  -- unit
  , (parse [sexp| unit |], Just (UnitVal, ""))
  -- lambda
  , (parse [sexp| (lambda (x) x) |], Just ((Closure "x" (Var "x") Map.empty, "")))
  -- nothing tests...
  , (parse [sexp| ("hi" "hi") |], Nothing)
  , (parse [sexp| (unit "hi") |], Nothing)
  , (parse [sexp| ("hi" unit) |], Nothing)
  , (parse [sexp| (unit unit) |], Nothing)
  , (parse [sexp| ((lambda (x) (y x)) "hi") |], Nothing)
  , (parse [sexp| ("hi" (lambda (x) (y x))) |], Nothing)
  , (parse [sexp| ((lambda (x) (y x)) unit) |], Nothing)
  , (parse [sexp| (unit (lambda (x) (y x))) |], Nothing)
  , (parse [sexp| (y (lambda (x) x)) |], Nothing)
  , (parse [sexp| ((lambda (x) x) y) |], Nothing)
  , (parse [sexp| (concat x "hi") |], Nothing)
  , (parse [sexp| (concat "hi" x) |], Nothing)
  , (parse [sexp| (concat x y) |], Nothing)
  , (parse [sexp| (concat unit "hi") |], Nothing)
  , (parse [sexp| (concat "hi" unit) |], Nothing)
  , (parse [sexp| (concat unit unit) |], Nothing)
  , (parse [sexp| (concat (lambda (x) x) "hi") |], Nothing)
  , (parse [sexp| (concat "hi" (lambda (x) x)) |], Nothing)
  , (parse [sexp| (concat (lambda (x) x) (lambda (x) x)) |], Nothing)
  , (parse [sexp| (output unit) |], Nothing)
  , (parse [sexp| (output (lambda (x) x)) |], Nothing)
  , (parse [sexp| (output x) |], Nothing)
  ]

e20 :: Exp
e20 = parse [sexp| ((lambda (f) (f " there")) (lambda (x) (concat "hi" x) )) |]

e30 :: Exp
e30 = parse [sexp| 
((lambda (s) (output (concat s " there"))) "hi")
|]

e40 :: Exp
e40 = parse [sexp| 
((lambda (s) (output (concat s " there"))) "hi")
|]

-- alpha variance
e50 :: Exp
e50 = parse [sexp| 
((lambda (s)
  ((lambda (s) (output s)) (concat s " there"))) "hi")
|]

e60 :: Exp
e60 = parse [sexp| 
((lambda (s)
  ((lambda (s) (output " there")) (output s))) "hi")
|]

-- scoping (this should error out)
e70 :: Exp
e70 = parse [sexp| 
((lambda (s)
  ((lambda (s) (output s)) (output s))) "hi")
|]

-- output order
e80 :: Exp
e80 = parse [sexp| 
  (
  ((lambda (x) (lambda (x) (output x))) (output "first"))
  ((lambda (x) " third") (output " second"))
  )
|]

runTest :: Exp -> Maybe (Val, String)
runTest e = eval e Map.empty

runTests :: [(Exp, Output)] -> [(Output, Output)]
runTests tests = (map (\(e, o) -> (runTest e, o)) tests)

assertTests :: [(Exp, Output)] -> [Bool]
assertTests tests = (map (\(e, o) -> (runTest e == o)) tests)

ppOutput :: IO ()
ppOutput = putStrLn (foldl
                     (\s (e, o) -> s ++ "\n" ++ (show e) ++ " == " ++ (show o))
                     ""
                     (runTests tests))

allOk :: Bool
allOk = foldl (\s i -> s && i) True (assertTests tests)

main :: IO ()
main = putStrLn $ show $ allOk
-- main = putStrLn $ show $ eval e1 Map.empty

----------------------------------------
----- parsing s-expressions for language
----------------------------------------
parse :: SExp -> Exp
parse   [sexp| unit |] = UnitLit
parse s@[sexp| lambda |] = error $ "bad 'lambda' expression: " ++ show s
parse s@[sexp| concat |] = error $ "bad 'concat' expression: " ++ show s
parse s@[sexp| output |] = error $ "bad 'output' expression: " ++ show s
parse   [sexp| @str:s |] = StringLit s
parse   [sexp| @sym:x |] = Var x
parse   [sexp| (lambda (@sym:x) @:e) |] = Lambda x (parse e)
parse s@[sexp| (lambda . @:_) |] = error $ "bad 'lambda' expression: " ++ show s
parse   [sexp| (concat @:e1 @:e2) |] = Concat (parse e1) (parse e2)
parse s@[sexp| (concat . @:_) =|] = error $ "bad 'concat' expression: " ++ show s
parse   [sexp| (output @:e) |] = Output (parse e)
parse s@[sexp| (output . @:_) |] = error $ "bad 'output' expression: " ++ show s
parse   [sexp| (@:e1 @:e2) |] = App (parse e1) (parse e2)
parse _ = error "could not parse s-expression into Exp"
