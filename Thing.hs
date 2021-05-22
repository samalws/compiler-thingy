import Data.List.Extra
import Control.Applicative
import Control.Monad
import Data.Maybe

-- TODO if statements on tagged unions

data PrimType = U8 | Flt deriving (Eq, Show)
-- TODO is recusion just gonna be cyclic vals or smth
data DataTypeDef = DataTypeDef { dtCtors :: [[Type]] } deriving (Eq, Show)
data Type = Prim PrimType | Data DataTypeDef deriving (Eq, Show)
data Expr = BadExpr | PrimIntExpr PrimType Integer | PrimFloatExpr PrimType Float | DataExpr DataTypeDef Int [Expr] | VarExpr Type String deriving (Eq, Show)
data Rhs  = IfRhs Type Cond Expr Expr | FnCallRhs Type String [Expr] | ExprRhs Expr deriving (Eq, Show)
data Cond = Cond Ordering Expr Expr deriving (Eq, Show)
data FnBody = FnBody { fnBodyArgs :: [(String, Type)], fnBodyReturn :: Type, fnBodyBody :: [(String, Rhs)] }

dummyVoidVal :: Expr
dummyVoidVal = BadExpr

extractExpr :: Maybe Expr -> Expr
extractExpr = maybe dummyVoidVal id

exprType :: Expr -> Type
exprType BadExpr = Prim U8
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

exprToInt :: Expr -> Integer
exprToInt (PrimIntExpr _ i) = i
exprToInt BadExpr = -1000
exprToInt _ = 0

exprToFloat :: Expr -> Float
exprToFloat (PrimFloatExpr _ f) = f
exprToFloat BadExpr = -1000
exprToFloat _ = 0

intBounds :: PrimType -> (Integer, Integer)
intBounds U8 = (0, 2^8)
intBounds _ = (0, 0)

inBounds :: (Ord a) => a -> (a, a) -> Bool
inBounds a (b, c) = a >= b && a < c

assignEnv :: (Eq a) => a -> b -> (a -> b) -> (a -> b)
assignEnv x y f z
  | z == x = y
  | otherwise = f z

checkExprValid :: (String -> Maybe Type) -> Expr -> Bool
checkExprValid _ (PrimIntExpr a b) = (isIntType a) && (inBounds b $ intBounds a)
checkExprValid _ (PrimFloatExpr a b) = isFloatType a
checkExprValid vars (DataExpr a b c) = all f (zip c t) && length c == length t where
  t = (dtCtors a) !! b
  f (x, y) = checkExprValid vars x && exprType x == y
checkExprValid vars (VarExpr a b) = vars b == pure a
checkExprValid _ BadExpr = False

checkCondValid :: (String -> Maybe Type) -> Cond -> Bool
checkCondValid vars (Cond ord e1 e2) = exprType e1 == exprType e2 && validExprs where
  validExprs = and $ map (checkExprValid vars) [e1,e2]

checkRhsValid :: (String -> Maybe Type) -> (String -> Maybe ([Type], Type)) -> Rhs -> Bool
checkRhsValid vars fns (IfRhs t c e1 e2) = sameTypes && validCond && validExprs where
  sameTypes = allSame $ t:(map exprType [e1,e2])
  validCond = checkCondValid vars c
  validExprs = and $ map (checkExprValid vars) [e1,e2]
checkRhsValid vars fns (FnCallRhs t f es) = allExprsValid && maybe False checkFn (fns f) where
  allExprsValid = and $ map (checkExprValid vars) es
  checkFn :: ([Type],Type) -> Bool
  checkFn (args, retVal) = retValEq && numArgsEq && argsMatchType where
    retValEq = t == retVal
    numArgsEq = length args == length es
    argsMatchType = and $ map (uncurry (==)) $ zip args $ map exprType es
checkRhsValid vars _ (ExprRhs e) = checkExprValid vars e

checkFnBodyValid :: (String -> Maybe ([Type], Type)) -> FnBody -> Bool
checkFnBodyValid fns fb = argsCheck && bodyCheck where
  args = fnBodyArgs fb
  argsCheck = length (nub $ map fst args) == length args
  startVars = flip lookup args
  bodyCheck = pure (fnBodyReturn fb) == (join $ fmap ($ "return") $ foldl f (pure startVars) $ fnBodyBody fb)
  f :: Maybe (String -> Maybe Type) -> (String, Rhs) -> Maybe (String -> Maybe Type)
  f mVars (s, rhs) = do
    vars <- mVars
    guard $ isNothing $ vars s
    guard $ isNothing $ fns  s
    guard $ checkRhsValid vars fns rhs
    pure $ assignEnv s (pure $ rhsType rhs) vars

checkFnBodyArgsValid :: FnBody -> [Expr] -> Bool
checkFnBodyArgsValid fb es = map snd (fnBodyArgs fb) == map exprType es

-- precondition: checkExprValid vars expr
evalExpr :: (String -> Expr) -> Expr -> Expr
evalExpr vars (VarExpr _ s) = vars s
evalExpr vars (DataExpr a b cs) = DataExpr a b $ map (evalExpr vars) cs
evalExpr _ x = x

-- precondition: checkCondValid vars cond
evalCond :: (String -> Expr) -> Cond -> Bool
evalCond vars (Cond ord e1 e2) = result where
  ee1 = evalExpr vars e1
  ee2 = evalExpr vars e2
  result = case (ee1, ee2) of
    (PrimIntExpr   _ a, PrimIntExpr   _ b) -> compare a b == ord
    (PrimFloatExpr _ a, PrimFloatExpr _ b) -> compare a b == ord
    _ -> True -- default value, should never happen

-- precondition: checkRhsValid vars fns rhs
evalRhs :: (String -> Expr) -> (String -> ([Expr] -> Expr)) -> Rhs -> Expr
evalRhs vars _ (IfRhs _ c e1 e2)
  | evalCond vars c = evalExpr vars e1
  | otherwise       = evalExpr vars e2
evalRhs vars fns (FnCallRhs _ f es) = fns f $ map (evalExpr vars) es
evalRhs vars _ (ExprRhs e) = evalExpr vars e

-- precondition: checkFnBodyValid fns fb && checkFnBodyArgsValid fb args
evalFnBody :: (String -> ([Expr] -> Expr)) -> FnBody -> [Expr] -> (String -> Maybe Expr)
evalFnBody fns fb args = foldl f argVars $ fnBodyBody fb where
  f :: (String -> Maybe Expr) -> (String, Rhs) -> (String -> Maybe Expr)
  f vars (s, rhs) = assignEnv s (pure $ evalRhs (extractExpr . vars) fns rhs) vars
  argVars :: String -> Maybe Expr
  argVars = foldr g (const empty) $ zip args $ fnBodyArgs fb
  g :: (Expr, (String, a)) -> (String -> Maybe Expr) -> (String -> Maybe Expr)
  g (e, (s, _)) vars = assignEnv s (pure e) vars

evalFnBodyReturn :: (String -> ([Expr] -> Expr)) -> FnBody -> [Expr] -> Expr
evalFnBodyReturn fns fb args = extractExpr $ evalFnBody fns fb args "return"

convertIntFn :: PrimType -> ([Integer] -> Integer) -> ([Expr] -> Expr)
convertIntFn t f = PrimIntExpr t . f . map exprToInt

convertFloatFn :: PrimType -> ([Float] -> Float) -> ([Expr] -> Expr)
convertFloatFn t f = PrimFloatExpr t . f . map exprToFloat

addU8 = convertIntFn U8 sum
defaultFn = const dummyVoidVal

u8t = Prim U8
fns = assignEnv "add" addU8 $ const defaultFn
fnTypes = assignEnv "add" (pure ([u8t, u8t], u8t)) $ const Nothing

u8e = PrimIntExpr U8

rhs1 = ExprRhs $ u8e 1
rhs2 = ExprRhs $ VarExpr u8t "d"
rhs3 = IfRhs u8t (Cond LT (VarExpr u8t "a") (VarExpr u8t "b")) (u8e 5) (u8e 6)
rhs4 = FnCallRhs u8t "add" [VarExpr u8t "c", VarExpr u8t "c"]

fnBody = FnBody [("d",u8t)] u8t [("a", rhs1), ("b", rhs2), ("c", rhs3), ("return", rhs4)]
