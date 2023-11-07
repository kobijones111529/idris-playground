module Test.NCurses

import NCurses as NC

export
main : IO ()
main = do
  _ <- NC.init
  _ <- NC.cBreak
  _ <- NC.noEcho
  NC.print "Hello"
  c <- NC.getChar
  NC.print $ show c
  _ <- NC.getChar
  NC.end
  pure ()
