--{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE GADTs, KindSignatures, TemplateHaskell, BangPatterns,
      FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
      UndecidableInstances, GeneralizedNewtypeDeriving,
      TypeSynonymInstances, ScopedTypeVariables, PatternSynonyms #-}

-- This module defines test cases for the unification algorithm, divided
-- into those which must succeed, those which should block (possibly
-- succeeding partially), and those which must fail.

module PatternUnify.Test where

import Unbound.LocallyNameless

import PatternUnify.Kit
import PatternUnify.Tm
import PatternUnify.Unify
import PatternUnify.Context
import PatternUnify.Check

import Debug.Trace (trace)

import Data.List (intercalate)


-- The |test| function executes the constraint solving algorithm on the
-- given metacontext.

test :: [Entry] -> IO ()
test = runTest (const True)


-- Allocate a fresh name so the counter starts from 1, to avoid clashing
-- with s2n (which generates names with index 0):

initialise :: Contextual ()
initialise = (fresh (s2n "init") :: Contextual (Name VAL)) >> return ()

prettyString t = render $ runPretty $ pretty t

solveEntries :: [Entry] -> Either Err ((), Context)
solveEntries !es  =
  let --intercalate "\n" $ map show es
    !initialContextString = render (runPretty (prettyEntries es))
    result = trace ("Initial context:\n" ++ initialContextString ) $
      runContextual (B0, map Right es) (initialise >> ambulando [] [] >> validate (const True))
    resultString = case result of
      Left _ -> "ERROR"
      Right (_, ctx) -> render $ runPretty $ pretty ctx
  in
    --trace ("\n\n=============\nFinal\n" ++ resultString)
      result



runTest :: (ProblemState -> Bool) -> [Entry] -> IO ()
runTest q es = do
                   putStrLn $ "Raw context:\n" ++ show (map show es)
                   putStrLn $ "Initial context:\n" ++
                                render (runPretty (prettyEntries es))

                   let r = runContextual (B0, map Right es)
                                       (initialise >> ambulando [] [] >> validate q)
                   case r of
                       Left err  -> putStrLn $ "Error: " ++ err
                       Right ((), cx)  -> putStrLn $ "Final context:\n" ++ pp cx ++ "\n"


runTestSolved, runTestStuck, runTestFailed :: IO ()
runTestSolved = mapM_ (runTest (== Solved)) tests
runTestStuck  = mapM_ (runTest (not . isFailed)) stucks
runTestFailed = mapM_ (runTest isFailed) fails

isFailed :: ProblemState -> Bool
isFailed (Failed _)  = True
isFailed _           = False

lifted :: Nom -> Type -> [Entry] -> [Entry]
lifted x _T es = lift [] es
   where
     lift :: Subs -> [Entry] -> [Entry]
     lift g (E a _A d : as) = E a (_Pi x _T (substs g _A)) d :
                                  lift ((a, meta a $$ var x) : g) as
     lift g (Prob a p s : as) = Prob a (allProb x _T (substs g p)) s : lift g as
     lift _ [] = []

boy :: String -> Type -> [Entry] -> [Entry]
boy = lifted . s2n

gal :: String -> Type -> Entry
gal x _T = E (s2n x) _T HOLE

eq :: String -> Type -> VAL -> Type -> VAL -> Entry
eq x _S s _T t = Prob (ProbId (s2n x)) (Unify (EQN _S s _T t)) Active

tests, stucks, fails :: [[Entry]]
tests = [

          -- test 0: solve B with A
          ( gal "A" SET
          : gal "B" SET
          : eq "p" SET (mv "A") SET (mv "B")
          : [])

          -- test 1: solve B with \ _ . A
        , ( gal "A" SET
          : gal "B" (mv "A" --> SET)
          : boy "x" (mv "A")
            ( eq "p" SET (mv "A") SET (mv "B" $$ vv "x")
            : [])
          )

          -- test 2: restrict B to second argument
        , ( gal "A" SET
          : boy "x" (mv "A")
            ( boy "y" (mv "A")
              ( gal "B" (mv "A" --> mv "A" --> SET)
              : eq "p" SET (mv "B" $$$ [vv "y", vv "x"])
                       SET (mv "B" $$$ [vv "x", vv "x"])
              : [])
            )
          )

          -- test 3: X unchanged
        , [ gal "X" (_PI "A" SET (vv "A" --> SET))
          , eq "p" SET (mv "X" $$$ [SET, SET])
                   SET (mv "X" $$$ [SET, SET])
          ]

          -- test 4: solve A with SET
        , [ gal "A" SET
          , eq "p" SET (mv "A") SET SET
          ]

          -- test 5: solve A with B -> B
        , [ gal "A" SET
          , gal "B" SET
          , gal "C" SET
          , eq "p" SET (mv "A") SET (mv "B" --> mv "B")
          ]

          -- test 6: solve A with \ X . B -> X
        , ( gal "A" (SET --> SET)
          : gal "B" SET
          : boy "X" SET
            ( eq "p" SET (mv "A" $$ vv "X") SET (mv "B" --> vv "X")
            : [])
          )

          -- test 7: solve A with \ _ X _ . B X -> X
        , ( gal "A" (SET --> SET --> SET --> SET)
          : gal "B" (SET --> SET)
          : boy "X" SET
            ( boy "Y" SET
              (eq "p" SET (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
                      SET (mv "B" $$ vv "X" --> vv "X")
              : [])
            )
          )

          -- test 8: solve S with A and T with B
        , [ gal "A" SET
          , gal "S" SET
          , gal "B" (mv "A" --> SET)
          , gal "T" (mv "S" --> SET)
          , eq "p" SET (PI (mv "A") (mv "B"))
                   SET (PI (mv "S") (mv "T"))
          ]

          -- test 9: solve M with \ y . y
        , [ gal "M" (SET --> SET)
          , eq "p" (SET --> SET) (ll "y" (vv "y"))
                   (SET --> SET) (ll "y" (mv "M" $$ vv "y"))
          ]

          -- test 10: solve A with \ _ X _ . X -> X and B with \ X _ _ . X
        , ( gal "A" (SET --> SET --> SET --> SET)
          : boy "X" SET
            ( boy "Y" SET
              ( gal "B" (SET --> SET)
              : eq "q" SET (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
                       SET (mv "B" $$ vv "Y" --> vv "X")
              : eq "p" SET (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
                       SET (vv "X" --> vv "X")
              : [])
            )
          )

          -- test 11: solve A with \ _ y . y
        , [ gal "A" (_PI "X" SET (vv "X" --> vv "X"))
          , eq "p" (_PI "X" SET (vv "X" --> vv "X")) (ll "X" (ll "y" (vv "y")))
                   (_PI "X" SET (vv "X" --> vv "X")) (ll "X" (mv "A" $$ vv "X"))
          ]

          -- test 12: solve f with \ _ y . y after lifting type
        , ( gal "f" (_PI "Y" SET (vv "Y" --> vv "Y"))
          : boy "X" SET
            ( eq "p" (vv "X" --> vv "X") (ll "y" (vv "y"))
                     (vv "X" --> vv "X") (mv "f" $$ vv "X")
            : [])
          )

          -- test 13: intersection with nonlinearity, restrict F to first two args
        , ( gal "F" (SET --> SET --> SET --> SET)
          : boy "X" SET
            ( boy "Y" SET
              ( eq "p" SET (mv "F" $$$ [vv "X", vv "X", vv "Y"])
                       SET (mv "F" $$$ [vv "X", vv "X", vv "X"])
              : [])
            )
          )

          -- test 14: heterogeneous equality; solve A and B with SET
        , [ gal "A" SET
          , gal "B" SET
          , eq "p" (mv "A" --> SET) (ll "a" SET)
                   (mv "B" --> SET) (ll "b" (mv "B"))
          , eq "q" SET (mv "A") SET (mv "B")
          ]

          -- test 15: sigma metavariable; solve A with ((?, Set), ?)
        , [ gal "A" (_SIG "X" (SET *: SET) (vv "X" %% Tl))
          , eq "p" SET SET SET (mv "A" %% Hd %% Tl)
          ]

          -- test 16: sigma variable; solve A with \ X Y . X * Y
        , ( gal "A" (SET --> SET --> SET)
          : boy "B" (_SIG "X" SET (vv "X" *: SET))
            ( eq "p" SET (mv "A" $$ (vv "B" %% Hd) $$ (vv "B" %% Tl %% Tl))
                     SET ((vv "B" %% Hd) *: (vv "B" %% Tl %% Tl))
            : [])
          )

          -- test 17: sigma variable; restrict A to \ _ X . ?A' X
        , ( gal "A" (SET --> SET --> SET)
          : boy "B" (_SIG "X" SET (vv "X" *: SET))
            ( eq "p" SET (mv "A" $$$ [vv "B" %% Hd, vv "B" %% Tl %% Tl])
                     SET (mv "A" $$$ [vv "B" %% Tl %% Tl, vv "B" %% Tl %% Tl])
            : [])
          )

          -- test 18: sigma variable; solve B with \ X z . ?A X (z -)
        , ( gal "A" (SET --> SET --> SET)
          : gal "B" (_PI "X" SET (vv "X" *: SET --> SET))
          : boy "C" (_SIG "X" SET (vv "X" *: SET))
            ( eq "p" SET (mv "A" $$$ [vv "C" %% Hd, vv "C" %% Tl %% Tl])
                     SET (mv "B" $$$ [vv "C" %% Hd, vv "C" %% Tl])
            : [])
          )

          -- test 19: sigma metavariable and equation; solve A
        , [ gal "A" (_SIG "X" SET (vv "X"))
          , eq "p" (_SIG "X" SET (vv "X" *: SET))
                       (PAIR (mv "A" %% Hd) (PAIR (mv "A" %% Tl) (SET --> SET)))
                   (_SIG "X" SET (vv "X" *: SET))
                       (PAIR (SET --> SET) (PAIR (ll "z" (vv "z")) (mv "A" %% Hd)))
          ]

          -- test 20: solve A with X ! and a with X -
        , ( boy "X" (_SIG "Y" SET (vv "Y"))
            ( gal "A" SET
            : gal "a" (mv "A")
            : eq "p" (_SIG "Y" SET (vv "Y")) (vv "X")
                     (_SIG "Y" SET (vv "Y")) (PAIR (mv "A") (mv "a"))
            : [])
          )

          -- test 21: solve A with f
        , ( boy "f" (SET --> SET)
            ( gal "A" (SET --> SET)
            : eq "p" (SET --> SET) (vv "f")
                     (SET --> SET) (ll "x" (mv "A" $$ vv "x"))
            : [])
          )

          -- test 22: solve A with SET
        , ( boy "X" ((SET --> SET) *: SET)
            ( gal "A" SET
            : eq "p" SET (vv "X" %% Hd $$ SET) SET (vv "X" %% Hd $$ mv "A")
            : [])
          )

          -- test 23: solve SS with [S', S']
        , ( gal "SS" (SET *: SET)
          : boy "f" (SET --> SET --> SET)
            ( eq "p" SET (vv "f" $$$ [mv "SS" %% Tl, mv "SS" %% Hd])
                     SET (vv "f" $$$ [mv "SS" %% Hd, mv "SS" %% Tl])
            : [])
          )

          -- test 24: solve A with SET
        , [ gal "A" SET
          , eq "p" (mv "A" --> SET) (ll "a" (mv "A"))
                   (SET --> SET) (ll "a" SET)
          ]

          -- test 25: solve with extensionality and refl
        , [ gal "A" SET
          , eq "p" (mv "A" --> SET) (ll "x" SET)
                   (SET --> SET) (ll "x" SET)
          ]

          -- test 26: solve A with \ _ Y . Y
        , ( gal "A" (SET --> SET --> SET)
          : boy "X" SET
            ( eq "p" (mv "A" $$ vv "X" $$ vv "X" --> SET)
                         (ll "Y" (mv "A" $$ vv "X" $$ vv "Y"))
                     (vv "X" --> SET)
                         (ll "Y" (vv "X"))
            : [])
          )

          -- test 27: solve A with SET
        , [ gal "A" SET
          , eq "p" SET (_PI "X" (SET --> SET) (vv "X" $$ mv "A"))
                   SET (_PI "X" (SET --> SET) (vv "X" $$ SET))
          ]

          -- test 28: prune and solve A with \ _ . B -> B
        , ( gal "A" (SET --> SET)
          : boy "x" (_SIG "Y" SET (vv "Y"))
            ( gal "B" SET
            : eq "p" SET (mv "A" $$ (vv "x" %% Hd))
                     SET (mv "B" --> mv "B")
            : [])
          )

          -- test 29: prune A and solve B with A
        , ( gal "A" (SET --> SET)
          : gal "B" SET
          : eq "p" (SET --> SET) (ll "X" (mv "A" $$ (vv "X" --> vv "X")))
                   (SET --> SET) (ll "X" (mv "B"))
          : [])

          -- test 30: prune A and solve B with A
        , ( gal "B" SET
          : gal "A" (SET --> SET)
          : eq "p" (SET --> SET) (ll "X" (mv "A" $$ (vv "X" --> vv "X")))
                   (SET --> SET) (ll "X" (mv "B"))
          : [])

          -- test 31: solve A with SET and f with \ x . x
        , ( gal "A" SET
          : gal "f" (mv "A" --> SET)
          : eq "p" (mv "A" --> SET) (mv "f")
                   (mv "A" --> mv "A") (ll "x" (vv "x"))
          : eq "q" SET (mv "A" --> SET) SET (mv "A" --> mv "A")
          : [])

          -- test 32: prune B and solve A with B -> B
        , ( gal "A" SET
          : gal "B" (SET --> SET)
          : eq "p" (SET --> SET) (ll "Y" (mv "A"))
                   (SET --> SET) (ll "X" ((mv "B" $$ mv "A") -->
                                               (mv "B" $$ vv "X")))
          : [])

          -- test 33: eta-contract pi
        , ( gal "A" ((SET --> SET) --> SET)
          : boy "f" (SET --> SET)
            ( eq "p" SET (mv "A" $$ (ll "y" (vv "f" $$ vv "y")))
                     SET (vv "f" $$ SET)
            : [])
          )

          -- test 34: eta-contract sigma
        , ( gal "A" (SET *: SET --> SET)
          : boy "b" (SET *: SET)
            ( eq "p" SET (mv "A" $$ (PAIR (vv "b" %% Hd) (vv "b" %% Tl)))
                     SET (vv "b" %% Hd)
            : [])
          )

          -- test 35: eta-contract pi and sigma
        , ( gal "A" ((SET *: SET --> SET) --> SET)
          : boy "f" (SET *: SET --> SET)
            ( eq "p" SET (mv "A" $$ (ll "b" (vv "f" $$ PAIR (vv "b" %% Hd) (vv "b" %% Tl))))
                     SET (vv "f" $$ PAIR SET SET)
            : [])
          )

          -- test 36: A/P Flattening Sigma-types
        , ( gal "u" ((SET --> SET *: SET) --> SET)
          : boy "z1" (SET --> SET)
            ( boy "z2" (SET --> SET)
              ( eq "p" SET (mv "u" $$ (ll "x" (PAIR (vv "z1" $$ vv "x") (vv "z2" $$ vv "x"))))
                       SET SET
              : [])
            )
          )

          -- test 37: A/P Eliminating projections
        , ( gal "u" ((SET --> SET) --> SET)
          : boy "y" (SET --> SET *: SET)
            ( eq "p" SET (mv "u" $$ (ll "x" (vv "y" $$ vv "x" %% Hd)))
                     SET (vv "y" $$ SET %% Hd)
            : [])
          )

          -- test 38: prune A and solve B with A
        , ( gal "B" SET
          : gal "A" (SET --> SET)
          : eq "p" (SET --> SET) (ll "X" (mv "B"))
                   (SET --> SET) (ll "X" (mv "A" $$ (vv "X" --> vv "X")))

          : [])

          -- test 39: solve u with \ _ x . x
        , ( gal "u" (_PI "v" (_SIG "S" SET (vv "S" *: (vv "S" --> SET))) ((vv "v" %% Tl %% Tl $$ (vv "v" %% Tl %% Hd)) --> (vv "v" %% Tl %% Tl $$ (vv "v" %% Tl %% Hd))))
          : boy "A" SET
            ( boy "a" (vv "A")
              ( boy "f" (vv "A" --> SET)
                ( eq "p" ((vv "f" $$ vv "a") --> (vv "f" $$ vv "a")) (mv "u" $$ PAIR (vv "A") (PAIR (vv "a") (vv "f")))
                         ((vv "f" $$ vv "a") --> (vv "f" $$ vv "a")) (ll "x" (vv "x"))
                : [])
              )
            )
          )

          -- test 40: restrict A to second argument
        , ( gal "A" (SET --> SET --> SET)
          : boy "X" SET
            ( boy "Y" SET
              ( eq "p" (SET --> SET) (mv "A" $$ vv "X")
                       (SET --> SET) (ll "Z" (mv "A" $$ vv "Y" $$ vv "Z"))
              : [])
            )
          )

          -- test 41: solve A with [ SET , SET ]
        , ( gal "A" (SET *: SET)
          : eq "p" (SET *: SET) (mv "A")
                   (SET *: SET) (PAIR (mv "A" %% Tl) SET)
          : [])

          -- test 42
        , ( gal "T" (SET --> SET)
          : gal "A" (_PI "Y" SET (mv "T" $$ vv "Y" --> SET))
          : gal "B" SET
          : boy "X" SET
            ( boy "t" (mv "T" $$ vv "X")
              ( eq "p" SET (mv "B") SET (mv "A" $$ vv "X" $$ vv "t" --> SET)
              : [])
            )
          )

          -- test 43
        , ( gal "A" (SET --> SET)
          : gal "F" (SET --> SET)
          : gal "B" SET
          : boy "X" SET
            ( eq "p" SET (mv "B")
                     SET (mv "A" $$ (mv "F" $$ vv "X") --> mv "A" $$ vv "X")
            : [])
          )

          -- test 44: false occurrence
        , ( gal "A" SET
          : gal "B" SET
          : gal "C" SET
          : eq "p" (mv "C" --> SET) (lamK (mv "B"))
                   (mv "C" --> SET) (lamK (mv "A"))
          : [])

          -- test 45
        , ( gal "A" SET
          : gal "B" (mv "A" --> SET)
          : gal "C" (mv "A" --> SET)
          : boy "x" (mv "A")
            ( boy "y" (mv "A")
              ( eq "p" SET (mv "B" $$ vv "x")
                       SET (mv "C" $$ vv "x")
              : [])
            )
          )

          -- test 46: prune p to learn B doesn't depend on its argument
        , ( gal "A" (SET --> SET)
          : boy "Z" SET
            ( gal "B" (SET --> SET)
            : gal "C" SET
            : boy "X" SET
              ( boy "Y" SET
                ( eq "p" SET (mv "A" $$ (mv "B" $$ mv "C"))
                         SET (mv "B" $$ vv "Y")
                : eq "q" SET (mv "B" $$ mv "C") SET (vv "Z")
                : [])
              )
            )
          )

          -- test 47
        , ( gal "A" (_PI "X" SET (vv "X" --> SET))
          : gal "B" SET
          : boy "Y" SET
            ( boy "y" (vv "Y")
              ( eq "p" SET (mv "B")
                       SET (mv "A" $$ vv "Y" $$ vv "y")
              : [])
            )
          )

          -- test 48
        , ( gal "A" (SET --> SET)
          : gal "B" SET
          : eq "p" SET (mv "B")
                   SET (_PI "X" SET (mv "A" $$ vv "X"))

          : [])

          -- test 49: don't prune A too much
        , ( gal "F" (SET --> SET --> SET)
          : gal "A" (_PI "X" SET (mv "F" $$ SET $$ vv "X" --> SET))
          : gal "B" (SET --> SET)
          : boy "Y" SET
            ( eq "p" (SET --> SET) (mv "B")
                     (mv "F" $$ SET $$ vv "Y" --> SET) (mv "A" $$ vv "Y")
            : boy "y" (mv "F" $$ SET $$ vv "Y")
              ( eq "q" SET (mv "F" $$ vv "Y" $$ vv "Y") SET SET
              : eq "r" SET (mv "A" $$ vv "Y" $$ vv "y")
                       (mv "F" $$ SET $$ vv "Y") (vv "y")
              : [])
            )
          )

          -- test 50: Miller's nasty non-pruning example
        , ( boy "a" SET
            ( gal "X" ((SET --> SET) --> SET --> SET)
            : boy "y" SET
              ( eq "p" SET (mv "X" $$ (ll "z" (vv "a")) $$ vv "y")
                       SET (vv "a")
              : eq "q" ((SET --> SET) --> SET --> SET) (mv "X")
                       ((SET --> SET) --> SET --> SET) (ll "z1" (ll "z2" (vv "z1" $$ vv "z2")))
              : [])
            )
          )

          -- test 51
        , ( gal "A" (_PI "X" SET (_PI "x" (vv "X") SET))
          : gal "B" SET
          : eq "p" SET (mv "B")
                   SET (_PI "X" SET (_PI "x" (vv "X") (mv "A" $$ vv "X" $$ vv "x")))
          : [])

        ]


stucks = [

          -- stuck 0: nonlinear
          ( gal "A" (SET --> SET --> SET --> SET)
          : gal "B" (SET --> SET)
          : boy "X" SET
            ( boy "Y" SET
              ( eq "p" SET (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
                       SET (mv "B" $$ vv "Y" --> vv "X")
              : [])
            )
          )

          -- stuck 1: nonlinear
        , ( gal "F" (SET --> SET --> SET)
          : gal "G" (SET --> SET --> SET)
          : boy "X" SET
            ( eq "p" SET (mv "F" $$$ [vv "X", vv "X"])
                     SET (mv "G" $$$ [vv "X", vv "X"])
            : [])
          )

          -- stuck 2: nonlinear
        , ( boy "X" SET
            ( gal "f" (vv "X" --> vv "X" --> vv "X")
            : boy "Y" SET
              ( boy "x" (vv "X")
                ( eq "p" (vv "Y" --> vv "X") (ll "y" (mv "f" $$ vv "x" $$ vv "x"))
                         (vv "Y" --> vv "X") (ll "y" (vv "x"))
                : [])
              )
            )
          )

          -- stuck 3: nonlinear
        , ( gal "B" (SET --> SET --> SET)
          : boy "X" SET
            ( gal "A" SET
            : eq "p" (mv "A" --> SET) (ll "a" (mv "B" $$ vv "X" $$ vv "X"))
                     (mv "A" --> SET) (ll "a" (vv "X"))
            : [])
          )

          -- stuck 4: double meta
        , [ gal "A" (SET --> SET)
          , gal "B" (SET --> SET)
          , gal "D" SET
          , gal "C" SET
          , eq "p" SET (mv "A" $$ (mv "B" $$ mv "C")) SET (mv "D")
          ]

          -- stuck 5: solution does not typecheck
        , ( gal "A" SET
          : gal "f" (mv "A" --> SET)
          : eq "p" (mv "A" --> SET) (mv "f")
                   (mv "A" --> mv "A") (ll "x" (vv "x"))
          : [])

          -- stuck 6: weak rigid occurrence should not cause failure
        , ( gal "A" ((SET --> SET) --> SET)
          : boy "f" (SET --> SET)
            ( eq "p" SET (mv "A" $$ vv "f")
                     SET (vv "f" $$ (mv "A" $$ (ll "X" (vv "X"))) --> SET)
            : [])
          )

          -- stuck 7: prune second argument of B and get stuck
        , ( gal "A" SET
          : gal "B" (SET --> SET --> SET)
          : boy "X" SET
            ( eq "p" SET (mv "A")
                     SET (mv "B" $$ mv "A" $$ vv "X")
            : [])
          )

          -- stuck 8: prune argument of A
        , ( boy "f" (SET --> SET)
            ( gal "A" (SET --> SET)
            : boy "X" SET
              ( boy "Y" SET
                ( eq "p" SET (mv "A" $$ vv "X")
                         SET (vv "f" $$ (mv "A" $$ vv "Y"))
                : [])
              )
            )
          )

          -- stuck 9 (requires sigma-splitting of twins)
        , ( gal "A" SET
          : gal "B" (SET --> mv "A" --> SET)
          : gal "S" SET
          : gal "T" (SET --> mv "S" --> SET)
          : eq "p" (SIG (mv "A") (mv "B" $$ SET) --> SET)
                        (ll "x" (mv "B" $$ SET $$ (vv "x" %% Hd)))
                    (SIG (mv "S") (mv "T" $$ SET) --> SET)
                        (ll "x" (mv "T" $$ SET $$ (vv "x" %% Hd)))
          : [])

          -- stuck 10: awkward occurrence (TODO: should this get stuck or fail?)
        , ( gal "A" SET
          : gal "a" (mv "A")
          : gal "f" (mv "A" --> SET)
          : eq "p" SET (mv "A") SET ((mv "f" $$ mv "a") --> SET)
          : [])

          -- stuck 12: twins with matching spines (stuck on B Set == T Set)
        , ( gal "A" SET
          : gal "B" (SET --> mv "A" --> SET)
          : gal "S" SET
          : gal "T" (SET --> mv "S" --> SET)
          : eq "p" (SIG (mv "A") (mv "B" $$ SET) --> mv "A")
                        (ll "x" (vv "x" %% Hd))
                    (SIG (mv "S") (mv "T" $$ SET) --> mv "S")
                        (ll "x" (vv "x" %% Hd))
          : [])

          -- stuck 13
        , ( gal "A" (SET --> SET)
          : gal "B" (SET --> SET)
          : gal "a" (mv "A" $$ SET)
          : gal "b" (mv "B" $$ SET)
          : eq "p" (SIG SET (mv "B")) (PAIR SET (mv "b"))
                   (mv "A" $$ SET)    (mv "a")
          : eq "q" SET (SIG SET (mv "B")) SET (mv "A" $$ SET)
          : [])

          -- stuck 14 (TODO: should this be solvable by pruning?)
        , ( gal "A" (SET --> SET)
          : gal "B" SET
          : boy "X" SET
            ( eq "p" SET (mv "A" $$ (mv "A" $$ vv "X"))
                     SET (mv "B")
            : [])
          )

          -- stuck 15
        , ( gal "F" (SET --> SET)
          : gal "A" (_PI "X" SET (mv "F" $$ vv "X"))
          : boy "X" SET
            ( boy "Y" SET
              ( eq "p" (mv "F" $$ vv "X") (mv "A" $$ vv "X")
                       (mv "F" $$ vv "Y") (mv "A" $$ vv "Y")
              : [])
            )
          )

          -- stuck 16
        , ( gal "B" (SET --> SET)
          : gal "F" (mv "B" $$ SET --> SET)
          : eq "p" (mv "B" $$ SET --> SET) (ll "Y" (mv "F" $$ vv "Y"))
                    (SET --> SET)           (ll "Y" (vv "Y"))
          : [])

          -- test 53: solve C with A despite B being in the way
        , ( gal "A" SET
          : gal "C" SET
          : gal "B" (SET --> SET)
          : gal "F" (mv "B" $$ SET --> SET)
          : eq "p" (_PI "X" (mv "B" $$ SET) ((mv "F" $$ vv "X") --> SET))
                       (ll "X" (ll "x" (mv "A")))
                   (_PI "X" SET (vv "X" --> SET))
                       (ll "X" (ll "x" (mv "C")))
          : [])

        ]

fails = [

          -- fail 0: occur check failure (A occurs in A -> A)
          [ gal "A" SET
          , eq "p" SET (mv "A") SET (mv "A" --> mv "A")
          ]

          -- fail 1: flex-rigid fails because A cannot depend on X
        , ( gal "A" SET
          : gal "B" SET
          : boy "X" SET
            ( eq "p" SET (mv "A") SET (mv "B" --> vv "X")
            : [])
          )

          -- fail 2: rigid-rigid clash
        , ( boy "X" SET
            ( boy "Y" SET
              ( eq "p" SET (vv "X") SET (vv "Y")
              : [])
            )
          )

          -- fail 3: spine mismatch
        , ( boy "X" (SET *: SET)
            ( eq "p" SET (vv "X" %% Hd) SET (vv "X" %% Tl)
            : [])
          )

          -- fail 4: rigid-rigid constant clash
        , ( eq "p" SET SET SET (SET --> SET)
          : [])

        ]
