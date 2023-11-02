module NCurses

libncurses : String -> String
libncurses f = "C:" ++ f ++ ",libncurses,ncurses.h"

%foreign libncurses "ncurses_err"
prim__err : PrimIO Int

%foreign libncurses "wresize"
prim__resizeWindow : AnyPtr -> Int -> Int -> PrimIO Int

export
data Window = Win AnyPtr

export
setWindowSize : HasIO io => Window -> (rows : Nat) -> (columns : Nat) -> io Bool
setWindowSize (Win win) rows columns = 
