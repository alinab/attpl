module LinCheck where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad (unless, when)
import Data.List (all)

newtype TypeErrorString = Err String deriving Show

type Check = Either TypeErrorString

type Sym = String

{- Type qualifiers -}
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
          | InL LinQual PreType Term
          | InR LinQual PreType Term
          | TCase Term Sym Term Sym Term
          | TRoll PreType Term
          | TUnRoll Term
          | TFunRec Sym Sym PreType PreType Term
          deriving (Eq, Show, Ord)

data PreType = TBool
             | TInt
             | TArr QualType QualType
             | TPair QualType QualType
             | TSum QualType QualType
             | TVar Sym
             | TRec Sym QualType
             deriving (Show, Eq, Ord)

{- Types with qualifiers; these wrap pre-types -}
data QualType = QualType LinQual PreType
          deriving (Eq, Show, Ord)

{- The context is an association lists of variables
 - associated with a qualified type -}
type Context = [(Sym, QualType)]

{-----------------------------------------------}

extend :: Context -> (String, QualType) -> Context
extend context vt = vt : context

delete :: Sym -> Context -> Context
delete v context = filter ((/= v ) . fst) context

{- Check that:
 - a term with a linear type is never present in an outgoing context
 - as that indicates that it is unused (linear -> always used once)
 - a term with unrestricted type is deleted from the context
 to ensure terms conform to scoping rules
-}
diffContext :: Context -> String -> QualType -> Check Context
diffContext context v qt = do
    case qt of
     (QualType Linear _) ->
        case lookup v context of
            Just _ -> throwError $ Err ("Linear Var: " ++  v ++ " unused")
            Nothing -> return context
     (QualType Unrestrict _) -> return (delete v context)

{- The containment check specifies that:
 - q(T) if and only if T = q'P where P is the pre-type
 - q ⊆ q' i.e. unrestricted data structures cannot contain linear data
 - strucutures or less restrictive data types must be contained within
 - more restrictive ones
-}
containCheck :: LinQual -> QualType -> Bool
containCheck lq qt =
  case (lq, qt) of
    (Linear, QualType Linear _) -> True
    (Unrestrict, QualType Unrestrict _) -> True
    (Unrestrict,  QualType Linear _ ) -> False

{- All linear types are consumed once when a term is type-checked
 - in the input context and unrestricted types pass through unchanged
 - (Unrestricted yariables introduced in lambdas and split terms are
 - deleted from the context so that they do not escape their scope.
-}
check :: Context -> Term -> Check (QualType, Context)
check context (Var x) =
  case lookup x context of
    Just qt@(QualType Unrestrict  _) -> return (qt, context)
    Just qt@(QualType Linear _) -> return (qt, delete x context)
    Nothing -> throwError $ Err "var not in context"

check context (Lam q symLam qt body) = do
    (bodyTy', context') <- check (extend context (symLam, qt)) body
    context'' <- diffContext context' symLam qt
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
      _otherFailure -> throwError $ Err "Condition in If term does not typecheck to a boolean"

check context (App t1 t2) = do
    (resultTy, context') <- check context t1
    case resultTy of
     QualType _  (TArr qt1 qt2) -> do
        (resultTy2, context'') <- check context' t2
        unless (resultTy2 == qt1) $ throwError $ Err "Type mismatch in App"
        return (qt2, context'')
     _otherFailure -> throwError $ Err "Trying to apply non-function"

check context (Pair qt t1 t2) = do
    (pairTy1, context') <- check context t1
    (pairTy2, context'')  <- check context' t2
    unless (containCheck qt pairTy1) $
        throwError $ Err "Containment check for first term of a Pair fails"
    unless (containCheck qt pairTy2) $
        throwError $ Err "Containment check for second term of a Pair fails"
    return (QualType qt (TPair pairTy1 pairTy2), context'')

check context (Split splitTerm symX symY inTerm) = do
    (splitTy, context') <- check context splitTerm
    case splitTy of
     QualType _ (TPair qt1 qt2) -> do
        let context'' = extend context' (symX, qt1)
        let context''' = extend context'' (symY, qt2)
        (typeRes, context'''') <- check context''' inTerm
        contextDiff1 <- diffContext context'''' symX qt1
        contextDiff2 <- diffContext contextDiff1 symY qt2
        return (typeRes, contextDiff2)
     _anyOtherFailure -> throwError $ Err "Cannot split a non-pair"


check context (LBool q _) = return (QualType q TBool, context)
check context (LInt q _) = return (QualType q TInt, context)

check context (InL qt pt inlTerm) = do
    (inlType, context') <- check context inlTerm
    case pt of
     TSum sumType1 sumType2 -> do
      unless (inlType == sumType1) $ throwError $
          Err "The left injection of the sum term does not match the assigned type"
      unless (containCheck qt sumType1) $ throwError $
          Err "Containment check for the left type of the sum type fails"
      unless (containCheck qt sumType2) $ throwError $
          Err "Containment check for the right type of the sum type fails"
      return (QualType qt (TSum sumType1 sumType2), context')
     _anyOtherType -> throwError $ Err "InL annotation is not a sum type"

check context (InR qt pt inrTerm) = do
    (inrType, context') <- check context inrTerm
    case pt of
     TSum sumType1 sumType2 -> do
         unless (inrType == sumType2) $ throwError $
            Err "The right injection of the sum term does not match the assigned type"
         unless (containCheck qt sumType1) $ throwError $
            Err "Containment check for the left type of the sum type fails"
         unless (containCheck qt sumType2) $ throwError $
            Err "Containment check for the right type of the sum type fails"
         return (QualType qt (TSum sumType1 sumType2), context')
     _anyOtherType -> throwError $ Err "InR annotation is not a sum type"

check context (TCase caseTerm symL inlTerm symR inrTerm) = do
    (caseTermTy, context') <- check context caseTerm
    case caseTermTy of
     QualType qt (TSum sumType1 sumType2) -> do
       let context' = extend context' (symL, sumType1)
       let context'' = extend context' (symR, sumType2)
       (inlType, contextL) <- check context' inlTerm
       (inrType, contextR) <- check context'' inrTerm
       contextDiffL <- diffContext contextL symL sumType1
       contextDiffR <- diffContext contextR symR sumType2
       unless (inlType == inrType) $ throwError $
        Err "The inferred types for the two case branches do not match"
       unless (contextDiffL == contextDiffR) $ throwError $
        Err "The type contexts for the two case branches differ"
       return (inlType, context')
     _anyOtherType -> throwError $ Err "Type for the case term does not evaluate to a sum type"

check context (TRoll pt rollTerm) =
    case pt of
     (TRec symRec innerTy@(QualType qt ptRec)) -> do
      (termTy, context') <- check context rollTerm
      -- qt also is the qualifier for the term replacing the inner type
      let recTypeUpdated = subsType symRec (QualType qt pt) innerTy
      unless (termTy == recTypeUpdated) $ throwError
        $ Err "Roll term type does not match unrolled type"
      return (QualType qt pt, context')
     _anyOtherType -> throwError $ Err "Roll term is not annotated with recursive type"

check context (TUnRoll unrollTerm) = do
    (ptRec, context') <- check context unrollTerm
    case ptRec of
     QualType _ pt@(TRec symRec (QualType qt ptRec)) -> do
      let recTypeUpdated = subsType symRec (QualType qt pt) (QualType qt ptRec)
      return (recTypeUpdated, context')
     _anyOtherType -> throwError $ Err "Unroll term is not annotated with recursive type"

check context (TFunRec symF symX pt1 qt2 recTerm) = do
    unless (all (\(_ , QualType q _) -> q == Unrestrict) context) $ throwError
        $ Err "Context is not free of linear types (for recursive functions)"
    let context' = extend context (symX, QualType Unrestrict pt1)
    -- The arrow/function type is from an unrestricted type to an unrestricted type
    let fTy = QualType Unrestrict (TArr (QualType Unrestrict pt1)
                            (QualType Unrestrict qt2))
    let context'' = extend context' (symF, fTy)
    (bodyTy, context''') <- check context'' recTerm
    case bodyTy of
      QualType Unrestrict utArr@(TArr ut1@(QualType Unrestrict _) qt') -> do
          unless (ut1 == QualType Unrestrict pt1) $ throwError $
            Err "The recursive function input type does not match the type annotation"
          unless (qt' == QualType Unrestrict qt2) $ throwError $
            Err "The recursive result type does not match the function output annotation type"
          contextDiffSymX <- diffContext context''' symX (QualType Unrestrict pt1)
          contextDiffSymR <- diffContext contextDiffSymX symF fTy
          return (QualType Unrestrict (TArr ut1 qt'), contextDiffSymR)
      _anyOtherType -> throwError $
            Err "The recursive result type does not match the function output type"

{- Type substituion -}
subsType sym replaceType qRecType =
    case qRecType of
      QualType qt (TVar sym') -> if sym' == sym then replaceType else
                                 QualType qt (TVar sym')
      QualType qt (TArr qtFuncP qtArgP) ->
        QualType qt (TArr (subsType sym replaceType qtFuncP) (subsType sym replaceType qtArgP))
      QualType qt (TPair qtPairFirst qtPairSecond) ->
              QualType qt (TPair (subsType sym replaceType qtPairFirst)
                        (subsType sym replaceType qtPairSecond))
      QualType qt (TSum qtSumLeft qtSumRight) ->
           QualType qt (TSum (subsType sym replaceType qtSumLeft)
                         (subsType sym replaceType qtSumRight))
      QualType qt (TRec sym' recType)
           | sym' == sym -> QualType qt (TRec sym recType)
           | otherwise -> QualType qt (TRec sym' (subsType sym replaceType recType))
      QualType qt TBool ->  QualType qt TBool
      QualType qt TInt ->  QualType qt TInt

checkExpr :: Term -> Either TypeErrorString (QualType, Context)
checkExpr = check []


{---------------------------------------------------------------}
type Store = [(Sym, Term)]

type Eval a = State (Store, Int) a

genSym :: Eval Sym
genSym = do
  (store, n) <- get
  put (store, n + 1)
  return ("x" ++ show n)

addStore :: Term -> Eval Sym
addStore term = do
                s <- genSym
                (store, n) <- get
                put ((s, term) : store, n)
                return s

delBindStore :: Sym -> Eval ()
delBindStore v = do
                 (store, n) <- get
                 put (filter ((/= v ) . fst) store, n)

lookupStore :: Sym -> Eval (Maybe Term)
lookupStore v = do
        (store, _) <- get
        return (lookup v store)

{- Variable substitution -}
substTerm :: Sym -> Sym -> Term -> Term
substTerm y x (Var z) = if z == y
                        then Var x else Var z
substTerm y x (App t1 t2) = App (substTerm y x t1) (substTerm y x t2)
substTerm y x (TIf t1 t2 t3) = TIf (substTerm y x t1) (substTerm y x t2)
                                    (substTerm y x t3)
substTerm y x (Lam q z qt body) = if z == y then Lam q z qt body
                                  else Lam q z qt (substTerm y x body)
substTerm y x (Pair q t1 t2)   = Pair q (substTerm y x t1) (substTerm y x t2)
substTerm y x (Split t a b body)  = Split (substTerm y x t) a b
                                    (if a == y || b == y
                                     then body
                                     else substTerm y x body)
substTerm _ _ t = t

{- Term evaluation -}
eval :: Term -> Eval Sym
eval (LBool q b) = addStore (LBool q b)
eval (LInt q n) = addStore (LInt q n)
eval (Var x) = return x

{- The terms in a pair are evaluated to variables; these variables are
 - then stored as a Pair term -}
eval (Pair qt t1 t2) = do
                       y <- eval t1
                       z <- eval t2
                       addStore (Pair qt (Var y) (Var z))

eval (Lam q x qt t) = addStore (Lam q x qt t)

{- t1 is evaluated to a Lambda and then t2 applied to it -}
eval (App t1 t2) = do
    x1 <- eval t1
    x2 <- eval t2
    result <- lookupStore x1
    case result of
        Just (Lam qt y _ l) -> do
          case qt of
           Linear -> delBindStore x1
           Unrestrict -> return ()
          eval (substTerm y x2 l)
        _otherFailure  -> error "App term incorrect-lambda not applied"

{- t1 is evaluated to a boolean pre-type before either t2 or t3 is
 - evaluated
-}
eval (TIf t1 t2 t3) = do
      x <- eval t1
      x' <- lookupStore x
      case x' of
        Just (LBool qt b) -> do
          case qt of
           Linear -> delBindStore x
           Unrestrict -> return ()
          case b of
            True -> eval t2
            False -> eval t3
        _otherFailure  -> error "If term condition is not a boolean"

{- The term to be split, t, is evaluated and checked to be a Pair term.
 - Substitutions for y and z by a and b respectively are before the
 - main term, inTerm, is evaluated
-}
eval (Split t a b inTerm) = do
    r <- eval t
    r' <- lookupStore r
    case r' of
        Just (Pair qt (Var y) (Var z)) -> do
          case qt of
           Linear -> delBindStore r
           Unrestrict -> return ()
          let t1 = substTerm a y inTerm
          let t2 = substTerm b z t1
          eval t2
        _otherFailure -> error "A non-pair term cannot be split"

{- All linear terms i.e. lambdas, pairs, booleans and integers are consumed
 - i.e. deallocated from the store at the top level after the entire term t
 - has been evaluated. Unrestricted variables remain as they are in the store
-}
runEval :: Term -> (Term, Store)
runEval t =
  let (sym, (store, _)) = runState (eval t) ([], 0) in
  case lookup sym store of
       Just v@(Lam Linear _ _ _) -> (v, filter ((/= sym) . fst) store)
       Just v@(Pair Linear _ _) -> (v, filter ((/= sym) . fst) store)
       Just v@(LInt Linear _) ->  (v, filter ((/= sym) . fst) store)
       Just v@(LBool Linear _) ->  (v, filter ((/= sym) . fst) store)
       Just v -> (v, store)
       Nothing -> error "Result not found in store"

runExample :: String -> Term -> IO ()
runExample name t = do
  putStr $ name ++ ": "
  case checkExpr t of
    Left err -> putStrLn $ "Type error: " ++ show err
    Right ty -> do
      let result = runEval t
      putStrLn $ show result ++ "  :  " ++ show ty

main :: IO ()
main = do
  putStrLn "=== Printing the output store value ===\n"

  putStrLn "\n=== Test 0 ===\n"
  runExample "Test: A Pair with linear values" $
    Pair Linear (LInt Linear 1) (LInt Linear 2)

  putStrLn "\n=== Test 1 ===\n"
  runExample "Test: Duplicating linear variable" $
    Split (Pair Linear (LInt Linear 1) (LInt Linear 2))
          "x" "y"
          (Pair Linear (Var "x") (Var "x"))

  putStrLn "\n=== Test 2 ===\n"
  runExample "Test: Unrestricted bool should be present in output store" $
    TIf (LBool Unrestrict True) (LInt Linear 1) (LInt Linear 2)

  putStrLn "\n=== Test 3 ===\n"
  runExample "App should deallocate linear lambda -> lambda \
                    \ should not be in output context" $
    App (Lam Linear "x" (QualType Linear TBool) (Var "x")) (LBool Linear True)

  putStrLn "\n=== Test 4 ===\n"
  {- This test is interesting because the linear ints in the initial Pair
   - are deallocated from the store. When the Split and Pair in the first line
   - are evaluated, variables a and b are freshly allocated
   - in the store and then substituted in the Pair term at the end.
   - The resulting linear Pair at the end has pointers to two distinct linear
   - variables which is acceptable. If the variabled were to be duplicated,
   - then an error would result as the same store location would be used twice.
   -}
  runExample "Test: Splitting and then pairing linear variables " $
    Split (Pair Linear (LInt Linear 1) (LInt Linear 2))
          "a" "b"
          (Pair Linear (Var "b") (Var "a"))


  putStrLn "\n=== Test 5 ===\n"
  {- All linear terms are consumed except for the linear True and linear False
   - values which are finally substituted for the terms of
   - the Pair returned at the end
  -}
  runExample "Test: Split, pair, split and then pair linear variables " $
    Split (Split (Pair Linear (LBool Linear True) (LBool Linear False))
          "a" "b"
           (Pair Linear (Var "b") (Var "a")))
           "e" "f"
           (Pair Linear -- the lambdas should not show up in the output store
           (App (Lam Linear "x" (QualType Linear TBool) (Var "x"))
               (Var "f"))
            (App (Lam Linear "x" (QualType Linear TBool) (Var "x"))
                        (Var "e")))
