||| System console terminal
||| 
||| Copyright 2021, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
||| 
module System.IO.Terminal

import Data.Buffer
import System.Info

import System.IO.Handle.Unix as U
import System.IO.Handle.Windows as W
import System.IO.Util.GetLine

%default total

-- ---------------------------------------------------------------------------

%foreign "scheme,chez:(foreign-procedure #f \"GetConsoleMode\" (void* u32*) int)"
         "C:GetConsoleMode,kernel32.dll"
         "javascript:lambda:(x, y) => 0"
prim__win_GetConsoleMode : AnyPtr -> Buffer -> PrimIO Int

%foreign "scheme,chez:(foreign-procedure #f \"GetConsoleMode\" (void* unsigned-32) int)"
         "C:SetConsoleMode,kernel32.dll"
         "javascript:lambda:(x, y) => 0"
prim__win_SetConsoleMode : AnyPtr -> (mode:Int) -> PrimIO Int

%foreign "scheme,chez:(foreign-procedure #f \"GetConsoleScreenBufferInfo\" (void* void*) int)"
         "C:GetConsoleScreenBufferInfo,kernel32.dll"
         "javascript:lambda:(x, y) => 0"
prim__win_GetConsoleScreenBufferInfo : AnyPtr -> Buffer -> PrimIO Int

-- ---------------------------------------------------------------------------

%foreign "C:ioctl,libc 6,sys/ioctl.h"
         "javascript:lambda:(x, y, z) => 0"
prim__ioctl_ptr : Int -> Bits32 -> Buffer -> PrimIO Int

-- ---------------------------------------------------------------------------

export setup : HasIO io => io Bool
setup =
  if elem codegen ["refc", "chez"] && os == "windows"
     then do
       Just b <- newBuffer 4
         | Nothing => pure False
       W.MkHandle h <- W.getStdout
       _ <- primIO $ prim__win_GetConsoleMode h b
       b' <- getInt32 b 0 >>= pure . prim__or_Int 0x0004
       _ <- primIO $ prim__win_SetConsoleMode h b'
       pure True
     else pure True


export getScreenSize : HasIO io => io (Maybe (Int, Int))
getScreenSize =
  if elem codegen ["refc", "chez"]
     then case os of
       "windows" => do
         Just b <- newBuffer 32
           | Nothing => pure Nothing
         W.MkHandle h <- W.getStdout
         _ <- primIO $ prim__win_GetConsoleScreenBufferInfo h b
         left   <- getBits16 b (5 * 2)
         top    <- getBits16 b (6 * 2)
         right  <- getBits16 b (7 * 2)
         bottom <- getBits16 b (8 * 2)
         pure $ Just (cast right - cast left + 1, cast bottom - cast top + 1)
       "unix" => do
         Just b <- newBuffer 8
           | Nothing => pure Nothing
         _ <- primIO $ prim__ioctl_ptr 0 (0x5413 {- TIOCGWINSZ -} ) b
         r <- getBits16 b 0
         c <- getBits16 b 2
         pure $ Just (cast c, cast r)
       _ => pure Nothing
     else pure Nothing


-- ---------------------------------------------------------------------------

export getChar : HasIO io => io (Maybe Char)
getChar = U.hGetChar U.stdin

export putChar : HasIO io => Char -> io ()
putChar ch = do
  _ <- U.hPutChar U.stdout ch
  pure ()

export getLine : HasIO io => io (Maybe String)
getLine = mkGetLine getChar 4096

export putStr : HasIO io => String -> io ()
putStr str = do
  _ <- U.hPutStr U.stdout str
  pure ()

export putStrLn : HasIO io => String -> io ()
putStrLn str = do
  _ <- U.hPutStrLn U.stdout str
  pure ()



-- ---------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
