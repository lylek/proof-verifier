{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Proof where

import Control.Monad (foldM, liftM2, unless)
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
    Truth
    | Falsehood
    | Formula :&: Formula
    | Formula :|: Formula
    | Formula :->: Formula
    | Formula :<->: Formula
    | Not Formula
    | ForAll Sym Formula
    | Exists Sym Formula
    | Term :=: Term
    | Rel Sym [Term]
    deriving (Eq, Show, Ord)

-- Propositional variables are just unary relations
pvar :: Sym -> Formula
pvar v = Rel v []

data Term =
    Var Sym
    | Const Sym
    | Func Sym [Term]
    deriving (Eq, Show, Ord)

data Sequent = Sequent
    { assumptions :: Set Formula
    , consequent :: Formula
    }
    deriving (Eq, Show)

freeVarsInFormula :: Formula -> Set Sym
freeVarsInFormula f = freeVarsInFormula' Set.empty f

freeVarsInFormula' :: Set Sym -> Formula -> Set Sym
freeVarsInFormula' boundVars f =
    case f of
        Truth -> Set.empty
        Falsehood -> Set.empty
        f1 :&: f2 -> Set.union (freeVarsInFormula' boundVars f1) (freeVarsInFormula' boundVars f2)
        f1 :|: f2 -> Set.union (freeVarsInFormula' boundVars f1) (freeVarsInFormula' boundVars f2)
        f1 :->: f2 -> Set.union (freeVarsInFormula' boundVars f1) (freeVarsInFormula' boundVars f2)
        f1 :<->: f2 -> Set.union (freeVarsInFormula' boundVars f1) (freeVarsInFormula' boundVars f2)
        Not f1 -> freeVarsInFormula' boundVars f1
        ForAll v f1 -> freeVarsInFormula' (Set.insert v boundVars) f1
        Exists v f1 -> freeVarsInFormula' (Set.insert v boundVars) f1
        f1 :=: f2 -> Set.union (freeVarsInTerm' boundVars f1) (freeVarsInTerm' boundVars f2)
        Rel _ fs -> Set.unions $ map (freeVarsInTerm' boundVars) fs

freeVarsInTerm :: Term -> Set Sym
freeVarsInTerm t = freeVarsInTerm' Set.empty t

freeVarsInTerm' :: Set Sym -> Term -> Set Sym
freeVarsInTerm' boundVars t =
    case t of
        Var v ->
            if Set.member v boundVars
                then Set.empty
                else Set.singleton v
        Const _ -> Set.empty
        Func _ fs -> Set.unions $ map (freeVarsInTerm' boundVars) fs

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
        IffIntro l -> do
            (p1, p2) <- twoPremises "IffIntro" premises
            let [as1, as2] = assumptionsPerAntecedent
            a1 <- assertJust (Map.lookup l (notYetCanceled as1)) $ T.concat
                [ "In left branch of IffIntro, did not find a preceding assumption with label "
                , T.pack $ show l
                ]
            a2 <- assertJust (Map.lookup l (notYetCanceled as2)) $ T.concat
                [ "In right branch of IffIntro, did not find a preceding assumption with label "
                , T.pack $ show l
                ]
            case conclusion of
                (cl :<->: cr) -> do
                    assert (a1 == cl) "In IffIntro, assumption to cancel in left branch must match left side of conclusion"
                    assert (p1 == cr) "In IffIntro, left premise must match right side of conclusion"
                    assert (a2 == cr) "In IffIntro, assumption to cancel in right branch must match right side of conclusion"
                    assert (p2 == cl) "In IffIntro, right premise must match left side of conclusion"
                    let as1' = as1 { notYetCanceled = Map.delete l $ notYetCanceled as1 }
                        as2' = as2 { notYetCanceled = Map.delete l $ notYetCanceled as2 }
                    ms <- mergeAssumptionState [as1', as2']
                    pure ms { canceledLabels = Set.insert l $ canceledLabels ms }
                _ -> Left "In IffIntro, conclusion must be a a bi-implication"
        NotIntro l -> do
            p <- onePremise "NotIntro" premises
            assert (p == Falsehood) $ "Premise in NotIntro must be Falsehood"
            let [as] = assumptionsPerAntecedent
            a <- assertJust (Map.lookup l (notYetCanceled as)) $ T.concat
                [ "In NotIntro, did not find a preceding assumption with label "
                , T.pack $ show l
                ]
            assert (conclusion == Not a) "In NotIntro, conclusion must be negation of assumption to cancel"
            pure as
                { notYetCanceled = Map.delete l $ notYetCanceled as
                , canceledLabels = Set.insert l $ canceledLabels as
                }
        RAA l -> do
            p <- onePremise "RAA" premises
            assert (p == Falsehood) $ "Premise in RAA must be Falsehood"
            let [as] = assumptionsPerAntecedent
            a <- assertJust (Map.lookup l (notYetCanceled as)) $ T.concat
                [ "In RAA, did not find a preceding assumption with label "
                , T.pack $ show l
                ]
            assert (a == Not conclusion) "In RAA, assumption to cancel must be negation of conclusion"
            pure as
                { notYetCanceled = Map.delete l $ notYetCanceled as
                , canceledLabels = Set.insert l $ canceledLabels as
                }
        IffElimLeft -> do
            (p1, p2) <- twoPremises "IffElimLeft" premises
            case p1 of
                (p1l :<->: p1r) -> do
                    assert (p1l == p2) "In IffElimLeft, second premise must match left side of first premise"
                    assert (p1r == conclusion) "In IffElimLeft, conclusion must match right side of first premise"
                    mergeAllAssumptionState
                _ -> Left "In IffElimLeft, first premise must be a bi-implication"
        IffElimRight -> do
            (p1, p2) <- twoPremises "IffElimRight" premises
            case p1 of
                (p1l :<->: p1r) -> do
                    assert (p1r == p2) "In IffElimRight, second premise must match right side of first premise"
                    assert (p1l == conclusion) "In IffElimRight, conclusion must match left side of first premise"
                    mergeAllAssumptionState
                _ -> Left "In IffElimRight, first premise must be a bi-implication"
        ForAllIntro -> do
            p <- onePremise "ForAllIntro" premises
            let [as] = assumptionsPerAntecedent
            case conclusion of
                (ForAll v f) -> undefined
                _ -> Left "In ForAllIntro, conclusion must be a universal quantification"
        ForAllElim -> undefined
        ExistsIntro -> undefined
        ExistsElim l -> undefined
        EqIntro -> undefined
        EqElim -> undefined
        EqSymmetric -> undefined
        EqTransitive -> undefined
        EqTerm -> undefined

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

matchFormulas :: Sym -> Formula -> Formula -> Either VerificationError [Term]
matchFormulas var quantifiedFormula formula =
    case (quantifiedFormula, formula) of
        (Truth, Truth) -> return []
        (Falsehood, Falsehood) -> return []
        (qf1 :&: qf2, f1 :&: f2) ->
            liftM2 (++) (matchFormulas var qf1 f1) (matchFormulas var qf2 f2)
        (qf1 :|: qf2, f1 :|: f2) ->
            liftM2 (++) (matchFormulas var qf1 f1) (matchFormulas var qf2 f2)
        (qf1 :->: qf2, f1 :->: f2) ->
            liftM2 (++) (matchFormulas var qf1 f1) (matchFormulas var qf2 f2)
        (qf1 :<->: qf2, f1 :<->: f2) ->
            liftM2 (++) (matchFormulas var qf1 f1) (matchFormulas var qf2 f2)
        (Not qf, Not f) -> matchFormulas var qf f
        (ForAll qv qf, ForAll v f) ->
            if qv == v
                then
                    if var == qv
                        then return [] -- the variable we are trying to match has been shadowed
                        else matchFormulas var qf f
                else Left "Mismatched universal quantifier variables in nested formulas"
        (Exists qv qf, Exists v f) ->
            if qv == v
                then if var == qv
                    then return [] -- the variable we are trying to match has been shadowed
                    else matchFormulas var qf f
                else Left "Mismatched existential quantifier variables in nested formulas"
        (qt1 :=: qt2, t1 :=: t2) ->
            liftM2 (++) (matchTerms var qt1 t1) (matchTerms var qt2 t2)
        (Rel qr qts, Rel r ts) -> do
            assert (qr == r) $ "Mismatched relation names in nested formulas"
            assert (length qts == length ts) $ "Mismatched relation argument list length in nested formulas"
            fmap concat $ mapM (uncurry (matchTerms var)) $ zip qts ts
        _ -> Left "Mismatched nested formulas"

matchTerms :: Sym -> Term -> Term -> Either VerificationError [Term]
matchTerms var quantifiedTerm term =
    case (quantifiedTerm, term) of
        (Var v, t) ->
            if var == v
                then return [t]
                else case t of
                    (Var tv) -> do
                        assert (v == tv) $ "Mismatched variable terms in nested terms"
                        return []
        (Const qc, Const c) -> do
            assert (qc == c) $ "Mismatched constant terms in nested terms"
            return []
        (Func qf qts, Func f ts) -> do
            assert (qf == f) $ "Mismatched function names in nested terms"
            assert (length qts == length ts) $ "Mismatched function argument list length in nested terms"
            fmap concat $ mapM (uncurry (matchTerms var)) $ zip qts ts
        _ -> Left "Mismatched nested terms"
