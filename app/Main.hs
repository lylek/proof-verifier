{-# LANGUAGE OverloadedStrings #-}

module Main where

import Proof

main :: IO ()
main = do
    print f1
    print $ freeVars f1
    print $ verify curryDerivation
    print $ verify orElim

f1 :: Formula
f1 = Var "y" :&: (ForAll "x" $ Var "x" :=: Var "x")

d1 :: Derivation
d1 =
    Inference
        { antecedents =
            [ Inference
                { antecedents =
                    [ Assumption
                        { formula = Var "a" :&: Var "b"
                        , cancellationLabel = Just 1
                        }
                    ]
                , conclusion = Var "a"
                , rule = AndElimLeft
                }
            ]
        , conclusion = (Var "a" :&: Var "b") :->: Var "a"
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
                                { formula = Var "a"
                                , cancellationLabel = Just 2
                                }
                            , Assumption
                                { formula = Var "b"
                                , cancellationLabel = Just 1
                                }
                            ]
                        , conclusion = Var "a" :&: Var "b"
                        , rule = AndIntro
                        }
                    ]
                , conclusion = Var "b" :->: (Var "a" :&: Var "b")
                , rule = ImpIntro 1
                }
            ]
        , conclusion = Var "a" :->: (Var "b" :->: (Var "a" :&: Var "b"))
        , rule = ImpIntro 2
        }

orElim :: Derivation
orElim =
    Inference
        { antecedents =
            [ Assumption
                { formula = Var "a" :|: Var "b"
                , cancellationLabel = Nothing
                }
            , Inference
                { antecedents =
                    [ Inference
                        { antecedents =
                            [ Assumption
                                { formula = Var "a" :->: Var "c"
                                , cancellationLabel = Nothing
                                }
                            , Assumption
                                { formula = Var "a"
                                , cancellationLabel = Just 1
                                }
                            ]
                        , conclusion = Var "c"
                        , rule = ImpElim
                        }
                    ]
                , conclusion = Var "c" :|: Var "d"
                , rule = OrIntroLeft
                }
            , Inference
                { antecedents =
                    [ Inference
                        { antecedents =
                            [ Assumption
                                { formula = Var "b" :->: Var "d"
                                , cancellationLabel = Nothing
                                }
                            , Assumption
                                { formula = Var "b"
                                , cancellationLabel = Just 1
                                }
                            ]
                        , conclusion = Var "d"
                        , rule = ImpElim
                        }
                    ]
                , conclusion = Var "c" :|: Var "d"
                , rule = OrIntroRight
                }
            ]
        , conclusion = Var "c" :|: Var "d"
        , rule = OrElim 1
        }
