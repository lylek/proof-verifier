{-# LANGUAGE OverloadedStrings #-}

module Main where

import Proof

main :: IO ()
main = do
    print f1
    print $ freeVarsInFormula f1
    print $ verify curryDerivation
    print $ verify orElim
    print $ matchFormulas "z" f3 f2

f1 :: Formula
f1 = pvar "A" :&: (ForAll "x" $ Var "x" :=: Var "x")

f2 :: Formula
f2 = (Var "x" :=: Var "t") :->: ((Var "y" :=: Var "t") :->: (Var "x" :=: Var "y"))

f3 :: Formula
f3 = (Var "x" :=: Var "z") :->: ((Var "y" :=: Var "z") :->: (Var "x" :=: Var "y"))

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
