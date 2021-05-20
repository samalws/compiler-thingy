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

dummyVoidVal :: Expr
dummyVoidVal = PrimIntExpr U8 0

extractExpr :: Maybe Expr -> Expr
extractExpr = maybe dummyVoidVal id

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

checkExprValidity :: (String -> Maybe Type) -> Expr -> Bool
checkExprValidity _ (PrimIntExpr a b) = (isIntType a) && (inBounds b $ intBounds a)
checkExprValidity _ (PrimFloatExpr a b) = isFloatType a
checkExprValidity vars (DataExpr a b c) = all f (zip c t) && length c == length t where
  t = (dtCtors a) !! b
  f (x, y) = checkExprValidity vars x && exprType x == y
checkExprValidity vars (VarExpr a b) = vars b == Just a

checkCondValidity :: (String -> Maybe Type) -> Cond -> Bool
checkCondValidity vars (Cond ord e1 e2) = exprType e1 == exprType e2 && validExprs where
  validExprs = and $ map (checkExprValidity vars) [e1,e2]

checkRhsValidity :: (String -> Maybe Type) -> (String -> Maybe ([Type], Type)) -> Rhs -> Bool
checkRhsValidity vars fns (IfRhs t c e1 e2) = sameTypes && validCond && validExprs where
  sameTypes = allSame $ t:(map exprType [e1,e2])
  validCond = checkCondValidity vars c
  validExprs = and $ map (checkExprValidity vars) [e1,e2]
checkRhsValidity vars fns (FnCallRhs t f es) = allExprsValid && maybe False checkFn (fns f) where
  allExprsValid = and $ map (checkExprValidity vars) es
  checkFn :: ([Type],Type) -> Bool
  checkFn (args, retVal) = retValEq && numArgsEq && argsMatchType where
    retValEq = t == retVal
    numArgsEq = length args == length es
    argsMatchType = and $ map (uncurry (==)) $ zip args $ map exprType es
checkRhsValidity vars _ (ExprRhs e) = checkExprValidity vars e

checkFnBodyValidity :: (String -> Maybe Type) -> (String -> Maybe ([Type], Type)) -> FnBody -> Bool
checkFnBodyValidity vars fns = isJust . foldr f (pure vars) . fnBodyBody where
  f :: (String, Rhs) -> Maybe (String -> Maybe Type) -> Maybe (String -> Maybe Type)
  f (s, rhs) mVars = do
    vars <- mVars
    guard $ isNothing $ vars s
    guard $ isNothing $ fns  s
    guard $ checkRhsValidity vars fns rhs
    pure $ assignEnv s (pure $ rhsType rhs) vars

evalExpr :: (String -> Expr) -> Expr -> Expr
evalExpr vars (VarExpr _ s) = vars s
evalExpr vars (DataExpr a b cs) = DataExpr a b $ map (evalExpr vars) cs
evalExpr _ x = x

evalCond :: (String -> Expr) -> Cond -> Bool
evalCond vars (Cond ord e1 e2) = result where
  ee1 = evalExpr vars e1
  ee2 = evalExpr vars e2
  result = case (ee1, ee2) of
    (PrimIntExpr   _ a, PrimIntExpr   _ b) -> compare a b == ord
    (PrimFloatExpr _ a, PrimFloatExpr _ b) -> compare a b == ord
    _ -> True -- default value, should never happen

evalRhs :: (String -> Expr) -> (String -> ([Expr] -> Expr)) -> Rhs -> Expr
evalRhs vars _ (IfRhs _ c e1 e2)
  | evalCond vars c = evalExpr vars e1
  | otherwise       = evalExpr vars e2
evalRhs _ fns (FnCallRhs _ f es) = fns f es
evalRhs vars _ (ExprRhs e) = evalExpr vars e

evalFnBody :: (String -> ([Expr] -> Expr)) -> FnBody -> (String -> Maybe Expr)
evalFnBody fns = foldr f (const empty) . fnBodyBody where
  f :: (String, Rhs) -> (String -> Maybe Expr) -> (String -> Maybe Expr)
  f (s, rhs) vars = assignEnv s (pure $ evalRhs (extractExpr . vars) fns rhs) vars
