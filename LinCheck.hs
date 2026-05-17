import Control.Monad.Except

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

diffContext :: Context -> String -> Context
diffContext context v qt = do
    case qt of
    (QualType Linear _) ->
        case (lookup v context) of
            Just _ -> throwError $ Err ("Linear Var" ++  v ++ " unused")
            Nothing -> return context
    (QualType Unrestricted _) -> return (delete v context)

{- All linear types are consumed when the term is type-checked in
 - the input context and unrestricted types pass through unchanged -}
check :: Context -> Term -> Check (QualType, Context)

check context (Var x) =
  case (lookup x context) of
    Just qt@(QualType Unrestricted  _)   -> return (qt, context)
    Just qt@(QualType Linear _) as  -> return (qt, (delete x context)
    Nothing -> throwError $ Err "var not in context"

check context (Lam q x qt body) = do
    (bodyTy', context') <- check (extend context (x, qt)) body
    context'' <- diffContext context' x qt
    when (q == Unrestricted) $ unless (context == context'') $
            throwError $ Err "Variables not captured in context"
    return (QualType q (TArr qt bodyTy'), context'')

check context (TIf t1 t2 t3) = do
    (boolTy, context') <- check context t1
    case boolTy of
    Qualtype _ TBool ->
         t1', context''  <- check context'' t2
         t2', context''' <- check context'' t3
         unless (t1' == t2')  $ throwError $ Err "Branch types differ"
         unless (context'' == context''')
                   $ throwError $ Err "Branch contexts differ"
         return (ty2, context'')
     _  -> throwError $ Err "Condition in If term does not typecheck to a boolean"

check context (App t1 t2) = do
    (resultTy, context') <- check context t1
    case resultTy of
     QualTpye _  (TArr qt1 qt2) -> do
        (resultTy2, context'') <- check context' t2
        unless (resultTy2 == qt1) $ throwError $ Err "Type mismatch in App"
        return (qt2, context'')
     _            -> throwError $ Err "Trying to apply non-function"

check context (Pair qt t1 t2) = do
    (pairTy1, context') <- check context t1
    (pairTy2, context'')  <- check context' t2
    return (QualType qt (TPair pairTy1 pairTy2), context'')

check context (Split splitTerm x y InTerm) = do
    (splitTy, context') <- check context splitTerm
    case splitTy of
    Qualtype _ TPair (qt1, qt2) ->
        (_ , context'') <- pure (extend context' (x, qty1))
        (_ , context''') <- pure (extend context' (y, qty2))
        (typeRes, context'''') <- check context''' Interm
        contextDiff1 <- diffContext context'''' x qt
        contextDiff2 <- diffContext contextDiff1 x qt
        return (typeRes, contextDiff2)
    _ -> throwError $ Err "Cannot split a non-pair"


check context (LBool q _) = return (QualType q TBool, context)
check context (LInt q _) = return (QualType q TInt, context)

{-----------------------------------------------}
checkExpr :: Term -> Either TypeError Type
checkExpr x = check [] x

