-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  portable
-----------------------------------------------------------------------------

module Utils (internalError) where

internalError :: String -> String -> String -> a
internalError moduleName functionName message = 
   error . unlines $
      [ ""
      , "INTERNAL ERROR - " ++ message
      , "** Module   : " ++ moduleName
      , "** Function : " ++ functionName
      ]
