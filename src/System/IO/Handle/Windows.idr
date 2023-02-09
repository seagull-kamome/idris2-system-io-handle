module System.IO.Handle.Windows

%default total


-- ---------------------------------------------------------------------------

%foreign "scheme,chez:(foreign-procedure #f \"GetStdHandle\" (unsigned-32) void*)"
         "RefC:GetStdHandle"
         "javascript:lambda:(x) => 0"
prim__win_GetStdHandle : Bits32 -> PrimIO AnyPtr

-- ---------------------------------------------------------------------------

public export data Handle = MkHandle AnyPtr

-- ---------------------------------------------------------------------------

export getStdin : HasIO io => io Handle
getStdin = pure $ MkHandle !(primIO $ prim__win_GetStdHandle $ cast (-10))

export getStdout : HasIO io => io Handle
getStdout = pure $ MkHandle !(primIO $ prim__win_GetStdHandle $ cast (-11))

export getStderr : HasIO io => io Handle
getStderr = pure $ MkHandle !(primIO $ prim__win_GetStdHandle $ cast (-13))


-- ---------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
