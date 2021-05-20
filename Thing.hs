import Data.List.Extra
import Control.Applicative
import Control.Monad
import Data.Maybe

-- TODO if statements on tagged unions
-- TOOD switch the order of function args so env is first

data PrimType = U8 | Flt deriving (Eq, Show)
-- TODO is recusion just gonna be cyclic vals or smth
data DataTypeDef = DataTypeDef { dtCtors :: [[Type]] } deriving (Eq, Show)
data Type = Prim PrimType | Data DataTypeDef deriving (Eq, Show)
data Expr = PrimIntExpr PrimType Integer | PrimFloatExpr PrimType Float | DataExpr DataTypeDef Int [Expr] | VarExpr Type String deriving (Eq, Show)
data Rhs  = IfRhs Type Cond Expr Expr | FnCallRhs Type String [Expr] | ExprRhs Expr deriving (Eq, Show)
data Cond = Cond Ordering Expr Expr deriving (Eq, Show)
data FnBody = FnBody { fnBodyArgs :: [Type], fnBodyReturn :: Type, fnBodyBody :: [(String, Rhs)] }

exprType :: Expr -> Type
exprType (PrimIntExpr a _) = Prim a
exprType (PrimFloatExpr a _) = Prim a
exprType (DataExpr a _ _) = Data a
exprType (VarExpr a _) = a

rhsType :: Rhs -> Type
rhsType (IfRhs a _ _ _) = a
rhsType (FnCallRhs a _ _) = a
rhsType (ExprRhs b) = exprType b

isPrimType :: Type -> Bool
isPrimType (Prim _) = True
isPrimType _ = False

isIntType :: PrimType -> Bool
isIntType x = x == U8

isFloatType :: PrimType -> Bool
isFloatType = not . isIntType

intBounds :: PrimType -> (Integer, Integer)
intBounds U8 = (0, 2^8)
intBounds _ = (0, 0)

inBounds :: (Ord a) => a -> (a, a) -> Bool
inBounds a (b, c) = a >= b && a < c

assignEnv :: (Eq a) => a -> b -> (a -> b) -> (a -> b)
assignEnv x y f z
  | z == x = y
  | otherwise = f z

checkExprValidity :: Expr -> (String -> Maybe Type) -> Bool
checkExprValidity (PrimIntExpr a b) _ = (isIntType a) && (inBounds b $ intBounds a)
checkExprValidity (PrimFloatExpr a b) _ = isFloatType a
checkExprValidity (DataExpr a b c) vars = all f (zip c t) && length c == length t where
  t = (dtCtors a) !! b
  f (x, y) = checkExprValidity x vars && exprType x == y
checkExprValidity (VarExpr a b) vars = vars b == Just a

checkCondValidity :: Cond -> (String -> Maybe Type) -> Bool
checkCondValidity (Cond ord e1 e2) vars = exprType e1 == exprType e2 && cv e1 && cv e2 where
  cv = flip checkExprValidity vars

checkRhsValidity :: Rhs -> (String -> Maybe Type) -> (String -> Maybe ([Type], Type)) -> Bool
checkRhsValidity (IfRhs t c e1 e2) vars fns = sameTypes && validCond && validExprs where
  sameTypes = allSame $ t:(map exprType [e1,e2])
  validCond = checkCondValidity c vars
  validExprs = cv e1 && cv e2
  cv = flip checkExprValidity vars
checkRhsValidity (FnCallRhs t f es) vars fns = allExprsValid && maybe False checkFn (fns f) where
  allExprsValid = and $ map (flip checkExprValidity vars) es
  checkFn :: ([Type],Type) -> Bool
  checkFn (args, retVal) = retValEq && numArgsEq && argsMatchType where
    retValEq = t == retVal
    numArgsEq = length args == length es
    argsMatchType = and $ map (uncurry (==)) $ zip args $ map exprType es
checkRhsValidity (ExprRhs e) vars _ = checkExprValidity e vars

checkFnBodyValidity :: FnBody -> (String -> Maybe Type) -> (String -> Maybe ([Type], Type)) -> Bool
checkFnBodyValidity fb vars fns = isJust $ foldr f (pure vars) $ fnBodyBody fb where
  f :: (String, Rhs) -> Maybe (String -> Maybe Type) -> Maybe (String -> Maybe Type)
  f (s, rhs) mVars = do
    vars <- mVars
    guard $ isNothing $ vars s
    guard $ isNothing $ fns  s
    guard $ checkRhsValidity rhs vars fns
    pure $ assignEnv s (pure $ rhsType rhs) vars

evalExpr :: Expr -> (String -> Expr) -> Expr
evalExpr (VarExpr _ s) env = env s
evalExpr (DataExpr a b cs) env = DataExpr a b $ map (flip evalExpr env) cs
evalExpr x _ = x

evalCond :: Cond -> (String -> Expr) -> Bool
evalCond (Cond ord e1 e2) env = result where
  ee1 = evalExpr e1 env
  ee2 = evalExpr e2 env
  result = case (ee1, ee2) of
    (PrimIntExpr   _ a, PrimIntExpr   _ b) -> compare a b == ord
    (PrimFloatExpr _ a, PrimFloatExpr _ b) -> compare a b == ord
    _ -> True -- default value, should never happen

evalRhs :: Rhs -> (String -> Expr) -> (String -> ([Expr] -> Expr)) -> Expr
evalRhs (IfRhs _ c e1 e2) vars _
  | evalCond c vars = evalExpr e1 vars
  | otherwise = evalExpr e2 vars
evalRhs (FnCallRhs _ f es) _ fns = fns f es
evalRhs (ExprRhs e) vars _ = evalExpr e vars

evalFnBody :: FnBody -> (String -> ([Expr] -> Expr)) -> (String -> Maybe Expr)
evalFnBody fb fns = foldr f (const empty) $ fnBodyBody fb where
  f :: (String, Rhs) -> (String -> Maybe Expr) -> (String -> Maybe Expr)
  f (s, rhs) vars = assignEnv s (pure $ evalRhs rhs (fromJust . vars) fns) vars
