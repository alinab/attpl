import Control.Monad.Except

data TypeError = Err String deriving Show

type Check = Either TypeError

type Sym = String

data Term = Var String
          | TIf Term Term Term
          | Lam Sym Type Term
          | App Term Term
          | LInt Int
          | LBool Bool
          deriving (Eq, Show, Ord)

data Type = TTrue
           | TFalse
           | TInt
           | TArr Type Type
          deriving (Show, Eq, Ord)

type Context = [(Sym, Type)]

extend :: Context -> (String, Type) -> Context
extend context vt = vt : context

check :: Context -> Term -> Check Type
check _ (LBool True) = return TTrue
check _ (LBool False) = return TFalse
check _ (LInt _) = return TInt

check context (TIf t1 t2 t3) = do
    result <- check context t1
    if result == TTrue then check context t2
    else check context t3

check context (Var x) = case (lookup x context) of
    Just a -> return a
    Nothing -> throwError $ Err "var not in context"

check env (Lam x t e) = do
    t' <- (check (extend env (x, t)) e)
    return (TArr t t')

check context (App e1 e2) = do
    t1 <- check context e1
    t2 <- check context e2
    case t1 of
      (TArr t1a t1b) | t1a == t2 -> return t1b
      (TArr t1a _) -> throwError $ Err "Type mismatch"
      _ -> throwError $ Err "Trying to apply non-function"

checkExpr :: Term -> Either TypeError Type
checkExpr x = check [] x



