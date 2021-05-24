import Data.List.Extra
import Control.Applicative
import Control.Monad
import Data.Maybe
import Safe
import Data.Bifunctor

-- TODO check that MatchRhs works


-- TYPE DEFINITIONS

data PrimType = U8 | Flt deriving (Eq, Show)
data DataTypeDef = DataTypeDef { dtName :: String, dtCtors :: [[Type]] }
data Type = Prim PrimType | Data DataTypeDef deriving (Eq, Show)
data Expr = BadExpr | PrimIntExpr PrimType Integer | PrimFloatExpr PrimType Float | DataExpr DataTypeDef Int [Expr] | VarExpr Type String deriving (Eq, Show)
data Rhs  = IfRhs Type Cond Expr Expr | MatchRhs Type Expr [(Expr, Expr)] | FnCallRhs Type String [Expr] | ExprRhs Expr deriving (Eq, Show)
data Cond = Cond Ordering Expr Expr deriving (Eq, Show)
data FnBody = FnBody { fnBodyArgs :: [(String, Type)], fnBodyRet :: Type, fnBodyBody :: [(String, Rhs)] }
data FnDef = FnDef String FnBody

-- so that we can have cyclic types and still test for equality and print
instance Eq DataTypeDef where
  a == b = dtName a == dtName b

instance Show DataTypeDef where
  show a = "DataTypeDef \"" <> dtName a <> "\""


-- BASIC FUNCTIONS

enclParens :: String -> String
enclParens s = "(" <> s <> ")"

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
rhsType (MatchRhs a _ _) = a
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

containsDups :: (Eq a) => [a] -> Bool
containsDups [] = False
containsDups (h:r) = elem h r || containsDups r

applyMatchToEnv :: Expr -> (String -> Maybe Type) -> (String -> Maybe Type)
applyMatchToEnv (VarExpr a b) vars = assignEnv b (pure a) vars
applyMatchToEnv (DataExpr _ _ a) vars = foldr applyMatchToEnv vars a
applyMatchToEnv _ vars = vars

-- match [first argument] { [second argument] => ... }
checkMatch :: Expr -> Expr -> Bool
checkMatch (VarExpr _ _) _ = True
checkMatch (PrimIntExpr _ a) (PrimIntExpr _ b) = a == b
checkMatch (PrimFloatExpr _ a) (PrimFloatExpr _ b) = a == b
checkMatch (DataExpr _ a bs) (DataExpr _ c ds) = and $ (a == c):(map (uncurry checkMatch) $ zip bs ds)
checkMatch _ _ = False


-- CHECKING VALIDITY

checkExprValid :: (String -> Maybe Type) -> Expr -> Bool
checkExprValid _ (PrimIntExpr a b) = (isIntType a) && (inBounds b $ intBounds a)
checkExprValid _ (PrimFloatExpr a b) = isFloatType a
checkExprValid vars (DataExpr a b c) = all f (zip c t) && length c == length t where
  t = (dtCtors a) !! b
  f (x, y) = checkExprValid vars x && exprType x == y
checkExprValid vars (VarExpr a b) = vars b == pure a
checkExprValid _ BadExpr = False

checkExprValidMatch :: (String -> Maybe Type) -> Expr -> Bool
checkExprValidMatch vars d@(DataExpr a b c) = all f (zip c t) && length c == length t && varsOnlyOnce where
  t = (dtCtors a) !! b
  f (x, y) = checkExprValidMatch vars x && exprType x == y
  varsOnlyOnce = not $ containsDups $ g d
  g (VarExpr _ s) = [s]
  g (DataExpr _ _ es) = mconcat $ fmap g es
  g _ = []
checkExprValidMatch vars (VarExpr _ b) = vars b == empty
checkExprValidMatch vars a = checkExprValid vars a

checkCondValid :: (String -> Maybe Type) -> Cond -> Bool
checkCondValid vars (Cond ord e1 e2) = exprType e1 == exprType e2 && validExprs where
  validExprs = and $ fmap (checkExprValid vars) [e1,e2]

checkRhsValid :: (String -> Maybe Type) -> (String -> Maybe ([Type], Type)) -> Rhs -> Bool
checkRhsValid vars _ (IfRhs t c e1 e2) = sameTypes && validCond && validExprs where
  sameTypes = allSame $ t:(fmap exprType [e1,e2])
  validCond = checkCondValid vars c
  validExprs = and $ fmap (checkExprValid vars) [e1,e2]
checkRhsValid vars _ (MatchRhs t m es) = sameRetTypes && sameMatchTypes && validMatchee && validMatches && validExprs where
  sameRetTypes = allSame $ t:(fmap (exprType . fst) es)
  sameMatchTypes = allSame $ fmap exprType $ m:(fmap snd es)
  validMatchee = checkExprValid vars m
  validMatches = and $ fmap (checkExprValidMatch vars . fst) es
  validExprs = and $ fmap f es
  f (match, ret) = checkExprValid (applyMatchToEnv match vars) ret
checkRhsValid vars fns (FnCallRhs t f es) = allExprsValid && maybe False checkFn (fns f) where
  allExprsValid = and $ fmap (checkExprValid vars) es
  checkFn :: ([Type],Type) -> Bool
  checkFn (args, retVal) = retValEq && numArgsEq && argsMatchType where
    retValEq = t == retVal
    numArgsEq = length args == length es
    argsMatchType = and $ fmap (uncurry (==)) $ zip args $ fmap exprType es
checkRhsValid vars _ (ExprRhs e) = checkExprValid vars e

checkFnBodyValid :: (String -> Maybe ([Type], Type)) -> FnBody -> Bool
checkFnBodyValid fns fb = argsCheck && bodyCheck && returnIsLast where
  args = fnBodyArgs fb
  argsCheck = length (nub $ fmap fst args) == length args
  startVars = flip lookup args
  bodyCheck = pure (fnBodyRet fb) == (join $ fmap ($ "return") $ foldl f (pure startVars) $ fnBodyBody fb)
  f :: Maybe (String -> Maybe Type) -> (String, Rhs) -> Maybe (String -> Maybe Type)
  f mVars (s, rhs) = do
    vars <- mVars
    guard $ isNothing $ vars s
    guard $ isNothing $ fns  s
    guard $ checkRhsValid vars fns rhs
    pure $ assignEnv s (pure $ rhsType rhs) vars
  returnIsLast = maybe False ((== "return") . fst) $ lastMay $ fnBodyBody fb

checkFnBodyArgsValid :: FnBody -> [Expr] -> Bool
checkFnBodyArgsValid fb es = fmap snd (fnBodyArgs fb) == fmap exprType es


-- EVALUATING

-- precondition: checkExprValid vars expr
evalExpr :: (String -> Expr) -> Expr -> Expr
evalExpr vars (VarExpr _ s) = vars s
evalExpr vars (DataExpr a b cs) = DataExpr a b $ fmap (evalExpr vars) cs
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
evalRhs vars _ (MatchRhs _ m es) = extractExpr $ headMay $ fmap snd $ filter fst $ fmap f es where
  f = bimap (checkMatch $ evalExpr vars m) (evalExpr vars)
evalRhs vars fns (FnCallRhs _ f es) = fns f $ fmap (evalExpr vars) es
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
convertIntFn t f = PrimIntExpr t . f . fmap exprToInt

convertFloatFn :: PrimType -> ([Float] -> Float) -> ([Expr] -> Expr)
convertFloatFn t f = PrimFloatExpr t . f . fmap exprToFloat


-- TO RUST

class ToRust a where
  toRust :: a -> String

instance ToRust PrimType where
  toRust U8 = "u8"
  toRust Flt = "f32"

instance ToRust DataTypeDef where
  toRust dt = "enum " <> dtName dt <> " { " <> options <> " }" where
    options = intercalate ", " optionList
    optionList = fmap f $ zip [0..] $ dtCtors dt
    f (n, ts) = "Opt" <> show n <> g ts
    g [] = ""
    g ts = enclParens $ intercalate ", " $ fmap toRust ts

instance ToRust Type where
  toRust (Prim t) = toRust t
  toRust (Data t) = dtName t

instance ToRust Expr where
  toRust BadExpr = "()"
  toRust (PrimIntExpr   t i) = show i <> toRust t
  toRust (PrimFloatExpr t f) = show f <> toRust t
  toRust (DataExpr t n es) = dtName t <> "::Opt" <> show n <> args where
    args
      | es == [] = ""
      | otherwise = enclParens $ intercalate ", " $ fmap toRust es
  toRust (VarExpr _ s) = s

instance ToRust Cond where
  toRust (Cond c a b) = enclParens (toRust a) <> cc <> enclParens (toRust b) where
    cc = case c of
      LT -> "<"
      GT -> ">"
      EQ -> "=="

instance ToRust Rhs where
  toRust (IfRhs _ c a b) = "if (" <> toRust c <> ") { " <> toRust a <> " } else { " <> toRust b <> " }"
  toRust (MatchRhs _ m es) = "match (" <> toRust m <> ") { " <> body <> " }" where
    body = intercalate ", " $ map f es
    f (a, b) = toRust a <> " => " <> toRust b
  toRust (FnCallRhs _ s es) = s <> (enclParens $ intercalate ", " $ fmap toRust es)
  toRust (ExprRhs e) = toRust e

instance ToRust FnDef where
  toRust (FnDef s fb) = "fn " <> s <> enclParens args <> " -> " <> ret <> " { " <> body <> " }" where
    args = intercalate ", " $ fmap f $ fnBodyArgs fb
    ret = toRust $ fnBodyRet fb
    body = intercalate "; " $ fmap g $ fnBodyBody fb
    f (s, t) = s <> ": " <> toRust t
    g ("return", e) = toRust e
    g (s, e) = "let " <> s <> " = " <> toRust e



-- TESTING

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
