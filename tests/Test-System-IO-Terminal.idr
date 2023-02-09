module Main

import System.IO.Terminal as Terminal

%default total

partial main : IO ()
main = do
  True <- Terminal.setup
          | _ => Prelude.putStrLn "Init failed."
  Terminal.getScreenSize >>= Terminal.putStrLn . show
  Terminal.putStr "01234567890"
  Terminal.putStrLn "ABCDEFGHIJKL"
  s <- Terminal.getLine
  Terminal.putStrLn $ "It's \"" ++ show s ++ "\""


