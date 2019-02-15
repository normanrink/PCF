
module Main


import PCF


main : IO ()
main = do x <- getLine
          let tx = natToTerm (cast x)
          printLn . termToNat . (\e => fst $ eval e) $ mul @.two @.tx
 
 
 
 
 
 
 
