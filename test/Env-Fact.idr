
module Main


import PCF


main : IO ()
main = do x <- getLine
          let tx = natToTerm (cast x)
          printLn . evalEnv $ fact @.tx
 
 
 
 
 
 
 
