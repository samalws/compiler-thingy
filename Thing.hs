import Data.List.Extra

-- TODO if statements on tagged unions

data PrimType = U8 | Flt deriving (Eq, Show)
-- TODO is recusion just gonna be cyclic vals or smth
data DataTypeDef = DataTypeDef { dtCtors :: [[Type]] } deriving (Eq, Show)
data Type = Prim PrimType | Data DataTypeDef deriving (Eq, Show)
data Expr = PrimIntExpr PrimType Integer | PrimFloatExpr PrimType Float | DataExpr DataTypeDef Int [Expr] | VarExpr Type String deriving (Eq, Show)
data Rhs  = IfRhs Type Cond Expr Expr | FnCallRhs Type String [Expr] | ExprRhs Expr deriving (Eq, Show)
data Cond = Cond Ordering Expr Expr deriving (Eq, Show)

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
checkRhsValidity (FnCallRhs t f es)
