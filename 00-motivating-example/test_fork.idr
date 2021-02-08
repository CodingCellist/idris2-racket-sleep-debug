-- Idris2

import System
import System.Concurrency

main : IO ()
main =
  do putStrLn "Hello"
     t <- fork $ do sleep 1
                    putStrLn "Wor"
                    sleep 2
     sleep 4
     putStrLn "ld"
     sleep 5

