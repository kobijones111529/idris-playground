module NCurses

libncurses : String -> String
libncurses f = "C:" ++ f ++ ",libncurses,ncurses.h"

%foreign libncurses "ncurses_err"
prim__err : PrimIO Int

%foreign libncurses "initscr"
prim__init : PrimIO AnyPtr

%foreign libncurses "endwin"
prim__end : PrimIO Int

%foreign libncurses "cbreak"
prim__cBreak : PrimIO Int

%foreign libncurses "noecho"
prim__noEcho : PrimIO Int

%foreign libncurses "printw"
prim__print : String -> PrimIO ()

%foreign libncurses "getch"
prim__getChar : PrimIO Int

%foreign libncurses "wresize"
prim__resizeWindow : AnyPtr -> Int -> Int -> PrimIO Int

export
data Window = Win AnyPtr

export
init : HasIO io => io Window
init = Win <$> primIO prim__init

export
end : HasIO io => io ()
end = primIO prim__end $> ()

export
cBreak : HasIO io => io Int
cBreak = primIO prim__cBreak

export
noEcho : HasIO io => io Int
noEcho = primIO prim__noEcho

export
print : HasIO io => String -> io ()
print = primIO . prim__print

export
getChar : HasIO io => io Int
getChar = primIO prim__getChar

export
setWindowSize : HasIO io => Window -> (rows : Nat) -> (columns : Nat) -> io Int
setWindowSize (Win win) rows columns =
  let
    rows = fromInteger $ natToInteger rows
    columns = fromInteger $ natToInteger columns
  in primIO $ prim__resizeWindow win rows columns
