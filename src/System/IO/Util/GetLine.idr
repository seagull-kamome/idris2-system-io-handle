||| GetLine
||| 
||| Copyright 2021, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
||| 
module System.IO.Util.GetLine

import Data.Buffer

%default total

-- ---------------------------------------------------------------------------

export mkGetLine' : HasIO io
                => (getc:io (Maybe Char))
                -> (buf:Buffer) -> (loc:Nat)
                -> io Nat
mkGetLine' getc buf loc = do
  bs <- rawSize buf
  if bs <= cast (natToInteger loc)
     then pure 0
     else go (fromInteger $ cast $ bs - cast loc) loc
  where
    go : Nat -> Nat -> io Nat
    go Z loc = pure loc
    go (S n) loc = do
      Just c <- getc
        | Nothing => pure loc
      if c == '\n'
         then pure loc
         else do
           setByte buf (cast loc) $ cast c
           go n (S loc)


export mkGetLine : HasIO io
               => (getc:io (Maybe Char))
               -> (maxlen:Nat)
               -> io (Maybe String)
mkGetLine getc maxlen = do
  Just b <- newBuffer (cast maxlen)
    | Nothing => pure Nothing
  newloc <- mkGetLine' getc b 0
  pure $ Just !(getString b 0 (cast newloc))


-- ---------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
