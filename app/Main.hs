{-# LANGUAGE OverloadedStrings #-}

module Main where

import Proof

main :: IO ()
main = do
    print f1
    print $ freeVarsInFormula f1
    print $ verify curryDerivation
    print $ verify orElim
    print $ matchFormulas "z" f3 f2 -- this is not a valid forall introduction
    print $ matchFormulas "z" f5 f4
    print $ verify breakRule5

f1 :: Formula
f1 = pvar "A" :&: (ForAll "x" $ Var "x" :=: Var "x")

f2 :: Formula
f2 = (Var "x" :=: Var "t") :->: ((Var "y" :=: Var "t") :->: (Var "x" :=: Var "y"))

f3 :: Formula
f3 = (Var "x" :=: Var "z") :->: ((Var "y" :=: Var "t") :->: (Var "x" :=: Var "y"))

-- forall introduction:
--  1) match quantified variable with terms
--  2) matched term must be the same each time it's matched
--  3) ignore shadowed occurrences as they are not the same variable
--  4) matched term must be a constant or variable
--  5) all free occurrences of matched term must be matched
--     in other words, the matched term must not appear free
--     in the quantified formula

-- An invalid inference - breaks rule #5
--            x = t -> y = t -> x = y
-- forall z . x = z -> y = t -> x = y

f4 :: Formula
f4 = (Var "x" :=: Var "t") :->: (ForAll "t" ((Var "y" :=: Var "t") :->: (Var "x" :=: Var "y")))

-- does not match the above, because in f5, the second z is still free, but in f4, the second t
-- is captured by a forall
f5 :: Formula
f5 = (Var "x" :=: Var "z") :->: (ForAll "t" ((Var "y" :=: Var "z") :->: (Var "x" :=: Var "y")))

d1 :: Derivation
d1 =
    Inference
        { antecedents =
            [ Inference
                { antecedents =
                    [ Assumption
                        { formula = pvar "A" :&: pvar "B"
                        , cancellationLabel = Just 1
                        }
                    ]
                , conclusion = pvar "A"
                , rule = AndElimLeft
                }
            ]
        , conclusion = (pvar "A" :&: pvar "B") :->: pvar "A"
        , rule = ImpIntro 1
        }

breakRule5 :: Derivation
breakRule5 =
    Inference
        { antecedents =
            [ Inference
                { antecedents =
                    [ Inference
                        { antecedents =
                            [ Inference
                                { antecedents =
                                    [ Assumption
                                        { formula = Var "x" :=: Var "t"
                                        , cancellationLabel = Just 2
                                        }
                                    , Inference
                                        { antecedents =
                                            [ Assumption
                                                { formula = Var "y" :=: Var "t"
                                                , cancellationLabel = Just 1
                                                }
                                            ]
                                        , conclusion = Var "t" :=: Var "y"
                                        , rule = EqSymmetric
                                        }
                                    ]
                                , conclusion = Var "x" :=: Var "y"
                                , rule = EqTransitive
                                }
                            ]
                        , conclusion = (Var "y" :=: Var "t") :->: (Var "x" :=: Var "y")
                        , rule = ImpIntro 1
                        }
                    ]
                , conclusion = (Var "x" :=: Var "t") :->: ((Var "y" :=: Var "t") :->: (Var "x" :=: Var "y"))
                , rule = ImpIntro 2
                }
            ]
        , conclusion = ForAll "z" ((Var "x" :=: Var "z") :->: ((Var "y" :=: Var "t") :->: (Var "x" :=: Var "y")))
        , rule = ForAllIntro
        }

curryDerivation :: Derivation
curryDerivation =
    Inference
        { antecedents =
            [ Inference
                { antecedents =
                    [ Inference
                        { antecedents =
                            [ Assumption
                                { formula = pvar "A"
                                , cancellationLabel = Just 2
                                }
                            , Assumption
                                { formula = pvar "B"
                                , cancellationLabel = Just 1
                                }
                            ]
                        , conclusion = pvar "A" :&: pvar "B"
                        , rule = AndIntro
                        }
                    ]
                , conclusion = pvar "B" :->: (pvar "A" :&: pvar "B")
                , rule = ImpIntro 1
                }
            ]
        , conclusion = pvar "A" :->: (pvar "B" :->: (pvar "A" :&: pvar "B"))
        , rule = ImpIntro 2
        }

orElim :: Derivation
orElim =
    Inference
        { antecedents =
            [ Assumption
                { formula = pvar "A" :|: pvar "B"
                , cancellationLabel = Nothing
                }
            , Inference
                { antecedents =
                    [ Inference
                        { antecedents =
                            [ Assumption
                                { formula = pvar "A" :->: pvar "C"
                                , cancellationLabel = Nothing
                                }
                            , Assumption
                                { formula = pvar "A"
                                , cancellationLabel = Just 1
                                }
                            ]
                        , conclusion = pvar "C"
                        , rule = ImpElim
                        }
                    ]
                , conclusion = pvar "C" :|: pvar "D"
                , rule = OrIntroLeft
                }
            , Inference
                { antecedents =
                    [ Inference
                        { antecedents =
                            [ Assumption
                                { formula = pvar "B" :->: pvar "D"
                                , cancellationLabel = Nothing
                                }
                            , Assumption
                                { formula = pvar "B"
                                , cancellationLabel = Just 1
                                }
                            ]
                        , conclusion = pvar "D"
                        , rule = ImpElim
                        }
                    ]
                , conclusion = pvar "C" :|: pvar "D"
                , rule = OrIntroRight
                }
            ]
        , conclusion = pvar "C" :|: pvar "D"
        , rule = OrElim 1
        }
