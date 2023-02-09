||| Unix file descriptor and lowlevel unbuffered IO.
||| 
||| Copyright 2021, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
||| 
module System.IO.Handle.Unix

import Data.List.Elem
import Data.Buffer
import Data.String

import public System.IO.Handle.Types
import System.IO.Util.GetLine


%default total

-- ---------------------------------------------------------------------------

export
data Handle : List Permission -> Type where
  MkHandle : {permission:List Permission} -> Int -> Handle permission

export stdin : Handle [Readable]
stdin = MkHandle 0

export stdout : Handle [Writable]
stdout = MkHandle 1

export stderr : Handle [Writable]
stderr = MkHandle 2

-- ---------------------------------------------------------------------------

%foreign "C:read,libc 6,unistd.h"
         "node:lambda:(fd,b,n) => require('fs').readSync(Number(fd), b, 0, Number(n))"
prim__unix_read_buffer : (fd:Int) -> (dst:Buffer) -> (bytes:Int) -> PrimIO Int

%foreign "C:write,libc 6,unistd.h"
         "node:lambda:(fd,b,n) => require('fs').writeSync(fd, b, {length:n})"
prim__unix_write_buffer : Int -> Buffer -> Int -> PrimIO Int
%foreign "C:write,libc 6,unistd.h"
         "node:lambda:(fd,s,n) => require('fs').writeSync(Number(fd), s, {length:Number(n)})"
prim__unix_write_string : Int -> String -> Int -> PrimIO Int

%foreign "C:ioctl,libc 6,sys/ioctl.h"
         "node:lambda:(fd,k,b) => require('ioctl').ioctl((Number(fd), k, b)"
prim__unix_ioctl_ptr : Int -> Bits32 -> Buffer -> PrimIO Int

%foreign "C:close,libc 6,unistd.h"
         "node:lambda:(fd) => require('fs').close(Number(fd))"
prim_unix_close : (fd:Int) -> PrimIO Int

-- ---------------------------------------------------------------------------
-- Buffer IO

export hRead' : HasIO io => Handle ps -> {auto 0 ok:Elem Readable ps}
             -> Buffer {- -> (ofs:Int) -} -> io Int
hRead' (MkHandle fd) b = do
  n <- rawSize b
  primIO $ prim__unix_read_buffer fd b n


export hRead : HasIO io => Handle ps -> {auto 0 ok:Elem Readable ps}
            -> (maxbytes:Nat)
            -> io (Maybe (Int, Maybe Buffer))
hRead h maxbytes = do
  Just b <- newBuffer (cast maxbytes)
    | Nothing => pure $ Nothing
  r <- hRead' h b
  if r <= 0
     then do
       pure $ Just (r, Nothing)
     else do
       pure $ Just (r, Just b)

export hWrite : HasIO io => Handle ps -> {0 ok:Elem Writable ps}
             -> Buffer -> (bytes:Nat) -> io Int
hWrite (MkHandle fd) b bytes = primIO $ prim__unix_write_buffer fd b (cast bytes)


-- ---------------------------------------------------------------------------
-- Char IO -- ofcourse very slow.

export hPutChar : HasIO io => Handle ps -> {auto 0 ok:Elem Writable ps}
               -> Char -> io Int
hPutChar (MkHandle fd) ch = do
  primIO $ prim__unix_write_string fd (singleton ch) 1

export hGetChar' : HasIO io => Handle ps -> {auto 0 ok:Elem Readable ps}
                -> io (Maybe (Either Int Char))
hGetChar' h = do
  Just (n, Just b) <- hRead h 1
    | Nothing => pure Nothing
    | Just (n, Nothing) => pure $ Just $ Left n
  ch <- getByte b 0
  pure $ Just $ Right $ cast{to=Char} ch


export hGetChar : HasIO io => Handle ps -> {auto 0 ok:Elem Readable ps}
               -> io (Maybe Char)
hGetChar h = do
  Just (Right ch) <- hGetChar' h
    | Nothing => pure Nothing
    | Just (Left _) => pure Nothing
  pure $ Just ch


-- ---------------------------------------------------------------------------
-- String IO


export hPutStr : HasIO io => Handle ps -> {auto 0 ok:Elem Writable ps}
              -> String -> io Int
hPutStr (MkHandle fd) str = do
  let n = cast $ length str
  primIO $ prim__unix_write_string fd str n

export hPutStrLn : HasIO io => Handle ps -> {auto 0 ok:Elem Writable ps}
               -> String -> io Int
hPutStrLn h str = hPutStr h $ str ++ "\n"

export hGetLine : HasIO io => Handle ps -> {auto 0 ok:Elem Readable ps}
               -> io (Maybe String)
hGetLine h = mkGetLine (hGetChar h) 4096


-- ---------------------------------------------------------------------------
-- open/close


export hClose : HasIO io => Handle ps -> io Int
hClose (MkHandle fd) = primIO $ prim_unix_close fd




-- ---------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
