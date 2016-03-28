{-# LANGUAGE EmptyDataDecls #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
--
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
--
-- Universal and existential quantification of types
--
-----------------------------------------------------------------------------

module Top.Types.Quantification () where

import Data.List
import Data.Maybe
import Top.Types.Primitive
import Top.Types.Substitution
import Utils (internalError)

import qualified PatternUnify.Tm as Tm
import qualified Unbound.Generics.LocallyNameless as Ln

-----------------------------------------------------------------------------
-- * Quantification
{-
newtype Quantification q a = Quantification ([Tm.Nom], QuantorMap, a)

type QuantorMap = [(Tm.Nom, String)]

withoutQuantors :: Quantification q a -> Bool
withoutQuantors (Quantification (is, _, _)) = null is

showQuantor :: Show q => Quantification q a -> String
showQuantor = show . f where
   f :: Quantification q a -> q
   f = internalError "Top.Types.Quantification" "showQuantor" "quantor unknown"

noQuantifiers :: a -> Quantification q a
noQuantifiers a = Quantification ([], [], a)

quantifiers :: Quantification q a -> [Tm.Nom]
quantifiers (Quantification (is, _, _)) = is

unquantify :: Quantification q a -> a
unquantify (Quantification (_, _, a)) = a

instance Substitutable a => Substitutable (Quantification q a) where
   sub |-> (Quantification (is, qmap, a)) = Quantification (is, qmap, removeDom is sub |-> a)
   ftv     (Quantification (is, _   , a)) = ftv a \\ is

instance HasTypes a => HasTypes (Quantification q a) where
   getTypes      (Quantification (_, _, a))     = getTypes a
   changeTypes f (Quantification (is, qmap, a)) = Quantification (is, qmap, changeTypes f a)

introduceTypeVariables :: Substitutable a => Tm.Nom -> Quantification q a -> (Tm.Nom, a)
introduceTypeVariables i (Quantification (qs, _, a)) = error "introduceTypeVariables"
  --  let sub = listToSubstitution (zip qs (map (Tm.var . Ln.s2n . show) [i..]))
  --  in (i + length qs, sub |-> a)

introduceSkolemConstants :: Substitutable a => Tm.Nom -> Quantification q a -> (Tm.Nom, a)
introduceSkolemConstants i (Quantification (qs, _, a)) = error "introduceSkolemConstants"
  --  let sub = listToSubstitution (zip qs (map (makeSkolemConstant . Ln.s2n . show) [i..]))
  --  in (i + length qs, sub |-> a)

bindTypeVariables :: Substitutable a => [Tm.Nom] -> a -> Quantification q a
bindTypeVariables is a = Quantification (is `intersect` ftv a, [], a)

bindSkolemConstants :: HasSkolems a => [Tm.Nom] -> a -> Quantification q a
bindSkolemConstants scs a =
   let scs'  = scs `union` allSkolems a
       skMap = [ (i, Tm.var i) | i <- scs' ]
   in Quantification (scs', [], changeSkolems skMap a)

getQuantorMap :: Quantification q a -> QuantorMap
getQuantorMap (Quantification (_, qm, _)) = qm

-----------------------------------------------------------------------------
-- * Universal quantification

data Universal
type Forall = Quantification Universal

instance Show Universal where
   show = const "forall"

instantiate, skolemize :: Substitutable a => Tm.Nom -> Forall a -> (Tm.Nom, a)
instantiate = introduceTypeVariables
skolemize   = introduceSkolemConstants

generalize :: (Substitutable context, Substitutable a) => context -> a -> Forall a
generalize context a =
   quantify (ftv a \\ ftv context) a

generalizeAll :: Substitutable a => a -> Forall a
generalizeAll a = quantify (ftv a) a

quantify :: Substitutable a => [Tm.Nom] -> a -> Forall a
quantify = bindTypeVariables

unskolemize :: HasSkolems a => [Tm.Nom] -> a -> Forall a
unskolemize = bindSkolemConstants

-----------------------------------------------------------------------------
-- * Existential quantification

data Existential
type Exists = Quantification Existential

instance Show Existential where
   show = const "exists"

open, reveal :: Substitutable a => Tm.Nom -> Exists a -> (Tm.Nom, a)
open   = introduceSkolemConstants
reveal = introduceTypeVariables

close :: HasSkolems a => [Tm.Nom] -> a -> Exists a
close = bindSkolemConstants

unreveal :: Substitutable a => [Tm.Nom] -> a -> Exists a
unreveal = bindTypeVariables

-----------------------------------------------------------------------------
-- * Skolemization

skolemPrefix :: String
skolemPrefix = "_"

makeSkolemConstant :: Tm.Nom -> Tm.VAL
makeSkolemConstant = error "makeSkolemConstant" --Tm.Con . (skolemPrefix++) . show

fromSkolemString :: String -> Maybe Tm.Nom
fromSkolemString s
   | skolemPrefix `isPrefixOf` s =
        Just (read (drop (length skolemPrefix) s))
   | otherwise = Nothing

skolemizeFTV :: Substitutable a => a -> a
skolemizeFTV a =
   let sub = listToSubstitution [ (i, makeSkolemConstant i) | i <- ftv a ]
   in sub |-> a

class HasSkolems a where
   allSkolems    :: a -> [Tm.Nom]
   changeSkolems :: [(Tm.Nom, Tm.VAL)] -> a -> a

instance HasSkolems Tm.VAL where
  --  allSkolems (TVar _)   = []
  --  allSkolems (TCon s)   = case fromSkolemString s of
  --                             Just i  -> [i]
  --                             Nothing -> []
  --  allSkolems (TApp l r) = allSkolems l `union` allSkolems r
   --
  --  changeSkolems skMap = rec where
  --     rec tp@(TVar _) = tp
  --     rec tp@(TCon s) = case fromSkolemString s of
  --                             Just i  -> fromMaybe tp (lookup i skMap)
  --                             Nothing -> tp
  --     rec (TApp l r)  = TApp (rec l) (rec r)

instance HasSkolems a => HasSkolems [a] where
   allSkolems = foldr (union . allSkolems) []
   changeSkolems skMap = map (changeSkolems skMap)

-----------------------------------------------------------------------------
-- * Pretty printing

data ShowQuantorOptions = ShowQuantorOptions
   { showTopLevelQuantors :: Bool
   , dontUseIdentifiers   :: [String]
   , variablePrefix       :: String
   , showAllTheSame       :: Bool
   , useTheNameMap        :: Bool
   }

defaultOptions :: ShowQuantorOptions
defaultOptions = ShowQuantorOptions
   { showTopLevelQuantors = False
   , dontUseIdentifiers   = []
   , variablePrefix       = "v"
   , showAllTheSame       = False
   , useTheNameMap        = True
   }

showQuantors :: ShowQuantors a => a -> String
showQuantors = showQuantorsWithout (defaultOptions { showTopLevelQuantors = True })

-- |This class can deal with the pretty printing of (possibly nested) quantifiers.
class Show a => ShowQuantors a where
   showQuantorsWithout :: ShowQuantorOptions -> a -> String

   -- default definition
   showQuantorsWithout = const show

instance ShowQuantors Tm.VAL

instance (Substitutable a, ShowQuantors a, Show q) => Show (Quantification q a) where
   show = showQuantorsWithout defaultOptions

instance (Substitutable a, ShowQuantors a, Show q) => ShowQuantors (Quantification q a) where
   showQuantorsWithout options q@(Quantification (is, qmap, a)) =
      let
          qs          = is `intersect` ftv a
          quantorText | null qs || not (showTopLevelQuantors options) = ""
                      | otherwise = unwords (showQuantor q : map (\i -> show (sub |-> Tm.var i)) qs ++ [". "])
          dontUse     = dontUseIdentifiers options
          -- find an appropriate name for bound type variables that are in the name map
          qmap1       | not (useTheNameMap options) || showAllTheSame options = []
                      | otherwise =
                           let op (rest, donts) (i,n)
                                  | i `elem` qs = let ints = [1..] :: [Int]
                                                      s :: Tm.Can
                                                      s = head [ n ++ extra
                                                               | extra <- "" : map show ints
                                                               , n ++ extra `notElem` donts
                                                               ]
                                                  in ((i,s):rest, s:donts)
                                  | otherwise   = (rest, donts)
                           in fst (foldl op ([], dontUse) qmap)
          dontUse1    = map snd qmap1 ++ dontUse
          -- find a name for the other bound type variables
          qmap2       | showAllTheSame options = []
                      | otherwise = zip (filter (`notElem` map fst qmap1) qs) (variableList \\ dontUse1)
          dontUse2    = map snd qmap2 ++ dontUse1
          frees       = ftv a \\ map fst (qmap1 ++ qmap2)
          sub         = listToSubstitution $  [ (i, Tm.Con s) | (i,s) <- qmap1 ++ qmap2 ]
                                           ++ [ (i, Tm.Con (variablePrefix options ++ show i)) | i <- frees ]
          newOptions  = options { dontUseIdentifiers   = dontUse2
                                , showTopLevelQuantors = True
                                }
      in
          quantorText ++ showQuantorsWithout newOptions (sub |-> a)

-- |List of unique identifiers.(a, b, .., z, a1, b1 .., z1, a2, ..)
variableList :: [String]
variableList =  [ [x]        | x <- ['a'..'z'] ]
             ++ [ x:show i | i <- [1 :: Int ..], x <- ['a'..'z'] ]
-}
