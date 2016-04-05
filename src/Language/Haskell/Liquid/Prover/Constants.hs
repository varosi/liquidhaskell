module Language.Haskell.Liquid.Prover.Constants where

-------------------------------------------------------------------------------
----------------------------   Debugging  -------------------------------------
-------------------------------------------------------------------------------

debug = True 
whenLoud act = if debug then act else return ()

-------------------------------------------------------------------------------
------------------------   Constant Numbers   ---------------------------------
-------------------------------------------------------------------------------

delta, epsilon, default_depth :: Int 
delta   = 5 
epsilon = 10 
default_depth = 2 


-------------------------------------------------------------------------------
------------------------   Files  ---------------------------------------------
-------------------------------------------------------------------------------

smtFileExtention = ".smt"
smtFile fn = fn ++ smtFileExtention
