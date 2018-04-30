{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Proof where

import Control.Monad (foldM, unless)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Debug.Trace (traceShowId)

type Sym = Text

type Label = Int

data Formula =
    Var Sym
    | Truth
    | Falsehood
    | Formula :&: Formula
    | Formula :|: Formula
    | Formula :->: Formula
    | Formula :<->: Formula
    | Not Formula
    | ForAll Sym Formula
    | Exists Sym Formula
    | Formula :=: Formula
    | Const Sym
    | Func Sym [Formula]
    | Rel Sym [Formula]
    deriving (Eq, Show, Ord)

data Sequent = Sequent
    { assumptions :: Set Formula
    , consequent :: Formula
    }
    deriving (Eq, Show)

freeVars :: Formula -> Set Sym
freeVars f =
    freeVars' Set.empty f
    where
        freeVars' boundVars f =
            case f of
                Var v ->
                    if Set.member v boundVars
                        then Set.empty
                        else Set.singleton v
                Truth -> Set.empty
                Falsehood -> Set.empty
                f1 :&: f2 -> Set.union (freeVars' boundVars f1) (freeVars' boundVars f2)
                f1 :|: f2 -> Set.union (freeVars' boundVars f1) (freeVars' boundVars f2)
                f1 :->: f2 -> Set.union (freeVars' boundVars f1) (freeVars' boundVars f2)
                f1 :<->: f2 -> Set.union (freeVars' boundVars f1) (freeVars' boundVars f2)
                Not f1 -> freeVars' boundVars f1
                ForAll v f1 -> freeVars' (Set.insert v boundVars) f1
                Exists v f1 -> freeVars' (Set.insert v boundVars) f1
                f1 :=: f2 -> Set.union (freeVars' boundVars f1) (freeVars' boundVars f2)
                Const _ -> Set.empty
                Func _ fs -> Set.unions $ map (freeVars' boundVars) fs
                Rel _ fs -> Set.unions $ map (freeVars' boundVars) fs

data Rule
    = TruthIntro
    | FalseElim
    | AndIntro
    | AndElimLeft
    | AndElimRight
    | OrIntroLeft
    | OrIntroRight
    | OrElim Label
    | ImpIntro Label
    | ImpElim
    | IffIntro Label
    | NotIntro Label
    | RAA Label
    | IffElimLeft
    | IffElimRight
    | ForAllIntro
    | ForAllElim
    | ExistsIntro
    | ExistsElim Label
    | EqIntro
    | EqElim
    | EqSymmetric
    | EqTransitive
    | EqTerm
    deriving (Eq, Show)

data Derivation =
    Assumption
        { formula :: Formula
        , cancellationLabel :: Maybe Label
        }
    | Inference
       { antecedents :: [Derivation]
       , conclusion :: Formula
       , rule :: Rule
       }

conclusionsOf :: [Derivation] -> [Formula]
conclusionsOf = map getConclusion
    where
        getConclusion Assumption{..} = formula
        getConclusion Inference{..} = conclusion

-- Later we may add more structured errors
type VerificationError = Text

data AssumptionState = AssumptionState
    { neverCanceled :: Set Formula
    , notYetCanceled :: Map Label Formula
    , canceledLabels :: Set Label
    }
    deriving (Show, Eq)

mergeAssumptionState :: [AssumptionState] -> Either VerificationError AssumptionState
mergeAssumptionState = foldM merge empty
    where
        merge a1 a2 = do
            let neverCanceled' = Set.union (neverCanceled a1) (neverCanceled a2)
            let canceledIn1Not2 = Set.intersection (Map.keysSet $ notYetCanceled a2) (canceledLabels a1)
            let canceledIn2Not1 = Set.intersection (Map.keysSet $ notYetCanceled a1) (canceledLabels a2)
            let canceledInOneButNotOther = Set.union canceledIn1Not2 canceledIn2Not1
            unless (Set.null canceledInOneButNotOther) $
                Left $ T.concat
                    [ "Formulas with each of the labels "
                    , T.intercalate ", " (map (T.pack . show) $ Set.toAscList canceledInOneButNotOther)
                    , " were canceled in one branch but not yet canceled in another branch"
                    ]
            let canceledInBoth = Set.intersection (canceledLabels a1) (canceledLabels a2)
            unless (Set.null canceledInBoth) $
                Left $ T.concat
                    [ "Formulas with each of the labels "
                    , T.intercalate ", " (map (T.pack . show) $ Set.toAscList canceledInBoth)
                    , " were canceled in two different branches"
                    ]
            let mergedNotYetCanceled =
                    Map.unionWith Set.union
                        (fmap Set.singleton (notYetCanceled a1))
                        (fmap Set.singleton (notYetCanceled a2))
            let conflictingAssumptionState =
                    Map.filter (\s -> Set.size s == 2) mergedNotYetCanceled
            unless (Map.null conflictingAssumptionState) $
                Left $ T.concat
                    [ "For each of the following labels, conflicting formulas were found: "
                    , T.intercalate ", " (map (T.pack .show) $ Map.keys conflictingAssumptionState)
                    ]
            pure $ AssumptionState
                { neverCanceled = neverCanceled'
                , notYetCanceled = fmap (Set.elemAt 0) mergedNotYetCanceled
                , canceledLabels = Set.union (canceledLabels a1) (canceledLabels a2)
                }
        empty =
            AssumptionState
                { neverCanceled = Set.empty
                , notYetCanceled = Map.empty
                , canceledLabels = Set.empty
                }

verify :: Derivation -> Either VerificationError Sequent
verify d = do
    as <- verify' d
    let [c] = conclusionsOf [d]
    pure $ Sequent { assumptions = neverCanceled as, consequent = c }

verify' :: Derivation -> Either VerificationError AssumptionState
verify' Assumption {..} = pure $
    case cancellationLabel of
        Nothing ->
            AssumptionState
                { neverCanceled = Set.singleton formula
                , notYetCanceled = Map.empty
                , canceledLabels = Set.empty
                }
        Just l ->
            AssumptionState
            { neverCanceled = Set.empty
            , notYetCanceled = Map.singleton l formula
            , canceledLabels = Set.empty
            }
verify' Inference {..} = do
    assumptionsPerAntecedent <- mapM verify' antecedents
    let mergeAllAssumptionState = mergeAssumptionState assumptionsPerAntecedent
    let premises = conclusionsOf antecedents
    case rule of
        TruthIntro -> do
            () <- noPremises "TruthIntro" premises
            assert (conclusion == Truth) $ T.append
                "Invalid conclusion for TruthIntro: " $ T.pack $ show conclusion
            mergeAllAssumptionState
        FalseElim -> do
            p <- onePremise "FalseElim" premises
            assert (p == Falsehood) $ "FalseElim's premise should be Falsehood"
            mergeAllAssumptionState
        AndIntro -> do
            (p1, p2) <- twoPremises "AndIntro" premises
            assert (conclusion == p1 :&: p2) $ "Conclusion of AndIntro is not conjunction of premises"
            mergeAllAssumptionState
        AndElimLeft -> do
            p <- onePremise "AndElimLeft" premises
            case p of
                pl :&: _ -> do
                    assert (conclusion == pl) $ "Conclusion of AndElimLeft should be left side of premise"
                    mergeAllAssumptionState
                _ -> Left "Premise of AndElimLeft should be a conjunction"
        AndElimRight -> do
            p <- onePremise "AndElimRight" premises
            case p of
                _ :&: pr -> do
                    assert (conclusion == pr) $ "Conclusion of AndElimRight should be right side of premise"
                    mergeAllAssumptionState
                _ -> Left "Premise of AndElimRight should be a conjunction"
        OrIntroLeft -> do
            p <- onePremise "OrIntroLeft" premises
            case conclusion of
                (cl :|: _) -> do
                    assert (cl == p) $ "In OrIntroLeft, left side of conclusion should match premise"
                    mergeAllAssumptionState
                _ -> Left "In OrIntroLeft, conclusion should be a disjunction"
        OrIntroRight -> do
            p <- onePremise "OrIntroRight" premises
            case conclusion of
                (_ :|: cr) ->
                    if cr == p
                        then mergeAllAssumptionState
                        else Left "In OrIntroRight, right side of conclusion should match premise"
                _ -> Left "In OrIntroRight, conclusion should be a disjunction"
        OrElim l -> do
            (disj, c1, c2) <- threePremises "OrElim" premises
            case disj of
                (dl :|: dr) -> do
                    assert (c1 == c2) "In OrElim, second and third premises must match"
                    assert (c1 == conclusion) "In OrElim, second and third premises must match conclusion"
                    let [as0, as1, as2] = assumptionsPerAntecedent
                    a1 <- assertJust (Map.lookup l (notYetCanceled as1)) $ T.concat
                        [ "In second antecedent of OrElim, did not find an assumption with label "
                        , T.pack $ show l
                        ]
                    assert (dl == a1) $ T.concat
                        [ "In OrElim with label "
                        , T.pack $ show l
                        , ", left side of disjunction must match assumption in second antecedent with that label"
                        ]
                    a2 <- assertJust (Map.lookup l (notYetCanceled as2)) $ T.concat
                        [ "In third antecedent of OrElim, did not find an assumption with label "
                        , T.pack $ show l
                        ]
                    assert (dr == a2) $ T.concat
                        [ "In OrElim with label "
                        , T.pack $ show l
                        , ", right side of disjunction must match assumption in third antecedent with that label"
                        ]
                    let as1' = as1 { notYetCanceled = Map.delete l $ notYetCanceled as1 }
                        as2' = as2 { notYetCanceled = Map.delete l $ notYetCanceled as2 }
                    ms <- mergeAssumptionState [as0, as1', as2']
                    pure ms { canceledLabels = Set.insert l $ canceledLabels ms }
                _ -> Left "In OrElim, first premise must be a disjunction"
        ImpIntro l -> do
            p <- onePremise "ImpIntro" premises
            let [as] = assumptionsPerAntecedent
            a <- assertJust (Map.lookup l (notYetCanceled as)) $ T.concat
                [ "In ImpIntro, did not find a preceding assumption with label "
                , T.pack $ show l
                ]
            case conclusion of
                (cl :->: cr) -> do
                    assert (a == cl) "In ImpIntro, assumption to cancel must match left side of conclusion"
                    assert (p == cr) "In ImpIntro, premise must match right side of conclusion"
                    pure $ AssumptionState
                       { neverCanceled = neverCanceled as
                       , notYetCanceled = Map.delete l $ notYetCanceled as
                       , canceledLabels = Set.insert l $ canceledLabels as
                       }
                _ -> Left "In ImpIntro, conclusion must be an implication"
        ImpElim -> do
            (p1, p2) <- twoPremises "ImpElim" premises
            case p1 of
                pl :->: pr ->
                    if pl == p2
                        then if pr == conclusion
                            then mergeAllAssumptionState
                            else Left "In ImpElim, right side of implication must match conclusion"
                        else Left "In ImpElim, left side of implication must match second premise"
                _ -> Left "In ImpElim, first premise must be an implication"
        _ -> mergeAllAssumptionState

noPremises :: Text -> [Formula] -> Either VerificationError ()
noPremises ruleName premises =
    case premises of
        [] -> Right ()
        _ -> Left (T.concat [ruleName, " should have no premises"])

onePremise :: Text -> [Formula] -> Either VerificationError Formula
onePremise ruleName premises =
    case premises of
        [p] -> Right p
        _ -> Left (T.concat [ruleName, " should have exactly one premise"])

twoPremises :: Text -> [Formula] -> Either VerificationError (Formula, Formula)
twoPremises ruleName premises =
    case premises of
        [p1, p2] -> Right (p1, p2)
        _ -> Left (T.concat [ruleName, " should have exactly two premises"])

threePremises :: Text -> [Formula] -> Either VerificationError (Formula, Formula, Formula)
threePremises ruleName premises =
    case premises of
        [p1, p2, p3] -> Right (p1, p2, p3)
        _ -> Left (T.concat [ruleName, " should have exactly three premises"])

assert :: Bool -> Text -> Either VerificationError ()
assert b msg = unless b $ Left msg

assertJust :: Maybe a -> Text -> Either VerificationError a
assertJust Nothing msg = Left msg
assertJust (Just v) _ = Right v
