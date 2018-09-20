-----------------------------------------------------------------------------
-- | License      :  GPL
--
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  portable
-----------------------------------------------------------------------------

module Top.Implementation.TypeGraph.Basics where

import Top.Implementation.TypeGraph.Path
--import Top.Types
import Utils (internalError)
-- import Data.Maybe
import Data.List (intercalate, partition, sort)
import qualified PatternUnify.Tm as Tm
import qualified Unbound.Generics.LocallyNameless as Ln

-----------------------------------------------------------------------------------------

data Constant = Con Tm.Can | ConElim Tm.CanElim | CApp | BoundVar Tm.Nom | NeutralTerm Tm.OrderedNeutral
  deriving (Eq, Ord, Show)

constantToTerm :: Constant -> Tm.VAL
constantToTerm c = error "TODO CTT"

newtype VertexId = VertexId Tm.Nom deriving (Eq, Ord)
type VertexInfo  = (VertexKind, Maybe Tm.VAL)
data VertexKind  =
  VVar
  | VCon Constant
  | VTerm
  | VApp VertexId VertexId
  | VertBot
   deriving (Show, Eq, Ord)

instance Show VertexId where
   show (VertexId i) = show i

vertexIdToTp :: VertexId -> Tm.VAL
vertexIdToTp (VertexId i) = Tm.var i

data EdgeId        = EdgeId VertexId VertexId EdgeNr
newtype EdgeNr     = EdgeNrX Tm.Nom deriving (Eq, Ord)
data ChildSide     = LeftChild | RightChild
   deriving (Eq, Ord)

makeEdgeNr :: Tm.Nom -> EdgeNr
makeEdgeNr = EdgeNrX

impliedEdgeNr :: EdgeNr
impliedEdgeNr = makeEdgeNr $ Ln.s2n (show $ -1)

instance Show EdgeNr where
   show (EdgeNrX i) = '#':show i

instance Show ChildSide where
   show LeftChild  = "(l)"
   show RightChild = "(r)"

data ParentChild = ParentChild { parent :: VertexId, child :: VertexId, childSide :: ChildSide }
   deriving Eq

instance Show ParentChild where
   show pc = show (child pc) ++ " <- " ++ show (parent pc) ++ show (childSide pc)

instance Ord ParentChild where
   compare pc1 pc2 = compare (child pc1, parent pc1) (child pc2, parent pc2)

type TypeGraphPath info = Path (EdgeId, PathStep info)
data PathStep info
   = Initial  info
   | Implied  ChildSide VertexId VertexId
   | Child    ChildSide

instance Show (PathStep info) where
   show (Initial _)      = "Initial"
   show (Implied cs x y) = "(" ++ show cs ++ " : " ++ show (x, y) ++ ")"
   show (Child i)        = "(" ++ show i ++ ")"

instance Show EdgeId where
   show (EdgeId a b _) = "("++show a++"-"++show b++")"
      -- where (a',b') = if a <= b then (a,b) else (b,a)

instance Eq EdgeId where -- why not compare the edge numbers here?
   EdgeId a b _ == EdgeId c d _ = (a == c && b == d) || (a == d && b == c)

instance Ord EdgeId where
   EdgeId a b _ <= EdgeId c d _ = order (a,b) <= order (c,d)
      where order (i,j) = if i <= j then (i,j) else (j,i)

-- A clique is a set of vertices that are equivalent because their parents are equal
-- Invariant: a clique cannot be empty
newtype Clique  = CliqueX [ParentChild]
type CliqueList = [Clique]

instance Show Clique where
   show (CliqueX xs) = "{" ++ intercalate ", " (map show xs) ++ "}"

instance Eq Clique where
   CliqueX xs == CliqueX ys =
      xs == ys

instance Ord Clique where
   compare (CliqueX xs) (CliqueX ys) = compare xs ys

isSubsetClique :: Clique -> Clique -> Bool
isSubsetClique (CliqueX as) (CliqueX bs) = rec as bs
 where
   rec [] _ = True
   rec _ [] = False
   rec a@(x:xs) (y:ys)
      | x == y    = rec xs ys
      | x > y     = rec a ys
      | otherwise = False

isDisjointClique :: Clique -> Clique -> Bool
isDisjointClique (CliqueX as) (CliqueX bs) = rec as bs
 where
   rec [] _ = True
   rec _ [] = True
   rec a@(x:xs) b@(y:ys)
      | x == y    = False
      | x > y     = rec a ys
      | otherwise = rec xs b

cliqueRepresentative :: Clique -> VertexId
cliqueRepresentative (CliqueX xs) =
   case xs of
      []  -> internalError "Top.TypeGraph.Basics" "cliqueRepresentative" "A clique cannot be empty"
      x:_ -> child x

triplesInClique :: Clique -> [ParentChild]
triplesInClique (CliqueX xs) = xs

childrenInClique :: Clique -> [VertexId]
childrenInClique = map child . triplesInClique

mergeCliques :: CliqueList -> Clique
mergeCliques list = CliqueX (foldr op [] [ xs | CliqueX xs <- list ])
 where
   op xs [] = xs
   op [] ys = ys
   op a@(x:xs) b@(y:ys)
      | x < y     = x : op xs b
      | x == y    = x : op xs ys
      | otherwise = y : op a ys

makeClique :: [ParentChild] -> Clique
makeClique list
   | length set < 2 = internalError "Top.TypeGraph.Basics" "makeClique" "incorrect clique"
   | otherwise      = CliqueX set
 where
   set = sort list

combineCliqueList :: CliqueList -> CliqueList -> CliqueList
combineCliqueList [] ys = ys
combineCliqueList (x:xs) ys =
   let (ys1, ys2) = partition (isDisjointClique x) ys
   in mergeCliques (x:ys2) : combineCliqueList xs ys1
