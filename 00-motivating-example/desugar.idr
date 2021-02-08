-- Idris2

import System
import System.Concurrency

child : IO ()
child =
  do sleep 1
     putStrLn "Wor"
     sleep 2


main : IO ()
main =
  do putStrLn "Hello"
     t <- fork child
     sleep 4
     putStrLn "ld"
     sleep 5

dchild : IO ()
dchild =
  sleep 1
  `io_bind` (\_ =>
  putStrLn "Wor"
  `io_bind` (\_ =>
  sleep 2
  ))

dmain : IO ()
dmain =
  putStrLn "Hello"
  `io_bind` (\_ =>
  fork child
  `io_bind` (\t =>
  sleep 4
  `io_bind` (\_ =>
  putStrLn "ld"
  `io_bind` (\_ =>
  sleep 5
  ))))

inline : IO ()
inline =
  putStrLn "Hello"
  `io_bind` (\_ =>
  fork (sleep 1
        `io_bind` (\_ =>
        putStrLn "Wor"
        `io_bind` (\_ =>
        sleep 2 ))
        )
  `io_bind` (\t =>
  sleep 4
  `io_bind` (\_ =>
  putStrLn "ld"
  `io_bind` (\_ =>
  sleep 5
  ))))

