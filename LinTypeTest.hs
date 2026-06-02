module LinTypeTest where

import LinCheck
import Test.QuickCheck
import Test.QuickCheck (Arbitrary)
import LinCheck (LinQual)
import Control.Monad.Except

type Name = String

data TypeError = UnboundVar Name
                | LinearVarReused Name
                | LinearVarUnused Name
                | ContainCheckFails QualType QualType
                | Mismatch QualType QualType
                | NotAFunction QualType
                | NotAPair QualType
                | NotASplit QualType
                deriving (Eq, Show)

typeCheck :: Context -> Term -> Either TypeError (QualType, Context)
typeCheck context (LBool q _) = return (QualType q TBool, context)
typeCheck context (LInt q _) = return (QualType q TInt, context)

typeCheck context (Var x) =
  case lookup x context of
    Just qt@(QualType Unrestrict  _) -> return (qt, context)
    Just qt@(QualType Linear _) -> return (qt, delete x context)
    Nothing -> throwError $ UnboundVar x

instance Arbitrary LinQual where
    arbitrary = elements [Linear, Unrestrict]

instance Arbitrary Term where
    arbitrary = sized genTerm
      where
        genTerm 0 = oneof
          [ Var <$> elements ["x", "y", "z"]
          , LBool <$> arbitrary <*> arbitrary
          , LInt <$> arbitrary <*> arbitrary
          ]
        genTerm n = frequency
                [ (1, Var   <$> elements ["x","y","z"])
                , (1, LBool <$> arbitrary <*> arbitrary)
                , (1, LInt  <$> arbitrary <*> arbitrary)
                , (2, TIf   <$> sub <*> sub <*> sub)
                , (2, App   <$> sub <*> sub)
                , (2, Pair  <$> arbitrary <*> sub <*> sub)
                ]
                 where sub = genTerm (n `div` 2)

prop_lbool_typechecks :: LinQual -> Bool -> Property
prop_lbool_typechecks q b =
  case typeCheck [] (LBool q b) of
    Right (QualType q' TBool, _) -> q === q'
    Left _                -> property False

prop_lint_typechecks :: LinQual -> Int -> Property
prop_lint_typechecks q n =
  case typeCheck [] (LInt q n) of
    Right (QualType q' TInt, _) -> q === q'
    Left _                -> property False


-- With an empty context, this test is set up to fail
prop_unboundVar_typechecks :: LinQual -> Int -> Property
prop_unboundVar_typechecks q uv =
    case typeCheck [] (Var "notbound") of
     Left (UnboundVar _) -> property True
     Right _              -> property False


main :: IO ()
main = do
    quickCheck prop_lbool_typechecks
    quickCheck prop_lint_typechecks
    quickCheck prop_unboundVar_typechecks


