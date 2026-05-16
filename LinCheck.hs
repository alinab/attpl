module LinCheck where

type Sym = String

data Term = Var String
          | TIf Term Term Term
          | Lam Sym Type Term
          | App Term Term
          | LInt Int
          | LBool Bool
          deriving (Eq, Show, Ord)

data Type = TBool
           | TInt
           | TArr Type Type
           | TErr
          deriving (Show, Eq, Ord)

type Context = [(Sym, Type)]

extend :: Context -> (String, Type) -> Context
extend context vt = vt : context

check :: Context -> Term -> Type
check _ (LBool _) = TBool
check _ (LInt _) = TInt
check context (TIf t1 t2 t3) =
    let result = check context t1 in
    if result == TBool then check context t2
    else check context t3

check context (Var x) = case (lookup x context) of
    Just a -> a
    Nothing -> TErr

check env (Lam x t e) =
    let t' = (check (extend env (x, t)) e) in
    TArr t t'

check context (App e1 e2) =
    let t1 = check context e1 in
    let t2 = check context e2 in
    case t1 of
      (TArr t1a t1b) | t1a == t2 -> t1b
      (TArr t1a _) -> TErr
      _ -> TErr







