import Control.Monad.Except
import Control.Monad

data TypeError = Err String deriving Show

type Check = Either TypeError

type Sym = String

data LinQual = Linear
             | Unrestrict
          deriving (Eq, Show, Ord)

data Term = Var String
          | TIf Term Term Term
          | Lam LinQual Sym QualType Term
          | Pair LinQual Term Term
          | App Term Term
          | LInt LinQual Int
          | LBool LinQual Bool
          | Split Term Sym Sym Term
          deriving (Eq, Show, Ord)

data PreType = TBool
             | TInt
             | TArr QualType QualType
             | TPair QualType QualType
             deriving (Show, Eq, Ord)

data QualType = QualType LinQual PreType
          deriving (Eq, Show, Ord)

type Context = [(Sym, QualType)]

{-----------------------------------------------}

extend :: Context -> (String, QualType) -> Context
extend context vt = vt : context

delete :: Sym -> Context -> Context
delete v context = filter ((/= v ) . fst) context

diffContext :: Context -> String -> QualType -> Check Context
diffContext context v qt = do
    case qt of
     (QualType Linear _) ->
        case (lookup v context) of
            Just _ -> throwError $ Err ("Linear Var: " ++  v ++ " unused")
            Nothing -> return context
     (QualType Unrestrict _) -> return (delete v context)


{- All linear types are consumed when the term is type-checked in
 - the input context and unrestricted types pass through unchanged -}
check :: Context -> Term -> Check (QualType, Context)

check context (Var x) =
  case (lookup x context) of
    Just qt@(QualType Unrestrict  _)   -> return (qt, context)
    Just qt@(QualType Linear _) -> return (qt, delete x context)
    Nothing -> throwError $ Err "var not in context"

check context (Lam q x qt body) = do
    (bodyTy', context') <- check (extend context (x, qt)) body
    context'' <- diffContext context' x qt
    when (q == Unrestrict) $ unless (context == context'') $
            throwError $ Err "Variables not captured in context"
    return (QualType q (TArr qt bodyTy'), context'')

check context (TIf t1 t2 t3) = do
    (boolTy, context') <- check context t1
    case boolTy of
      QualType _ TBool -> do
         (t1', context'') <- check context' t2
         (t2', context''') <- check context' t3
         unless (t1' == t2')  $ throwError $ Err "Branch types differ"
         unless (context'' == context''')
                   $ throwError $ Err "Branch contexts differ"
         return (t2', context'')
      _  -> throwError $ Err "Condition in If term does not typecheck to a boolean"

check context (App t1 t2) = do
    (resultTy, context') <- check context t1
    case resultTy of
     QualType _  (TArr qt1 qt2) -> do
        (resultTy2, context'') <- check context' t2
        unless (resultTy2 == qt1) $ throwError $ Err "Type mismatch in App"
        return (qt2, context'')
     _            -> throwError $ Err "Trying to apply non-function"

check context (Pair qt t1 t2) = do
    (pairTy1, context') <- check context t1
    (pairTy2, context'')  <- check context' t2
    return (QualType qt (TPair pairTy1 pairTy2), context'')

check context (Split splitTerm x y inTerm) = do
    (splitTy, context') <- check context splitTerm
    case splitTy of
     QualType _ (TPair qt1 qt2) -> do
        let context'' = extend context' (x, qt1)
        let context''' = extend context'' (y, qt2)
        (typeRes, context'''') <- check context''' inTerm
        contextDiff1 <- diffContext context'''' x qt1
        contextDiff2 <- diffContext contextDiff1 y qt2
        return (typeRes, contextDiff2)
     _ -> throwError $ Err "Cannot split a non-pair"


check context (LBool q _) = return (QualType q TBool, context)
check context (LInt q _) = return (QualType q TInt, context)

{-----------------------------------------------}
checkExpr :: Term -> Either TypeError (QualType, Context)
checkExpr x = check [] x

