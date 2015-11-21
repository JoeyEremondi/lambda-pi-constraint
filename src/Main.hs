import qualified Original as O
import qualified ConstraintBased as CB
import Common

main :: IO ()
main = repLP CB.checker True
