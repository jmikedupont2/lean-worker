import Gokujo

/-!
# `gokujo`, the executable

The root `main` `lake` needs, kept out of `Gokujo.lean` so that the library can be
imported by other programs that have a `main` of their own.

The import was `RequestProject.Tracker.Gokujo`, which only exists in the
tracker-side tree (lean/RequestProject/Tracker/Gokujo.lean) — inside this
minimal package the module is plain `Gokujo`, so the old import made every
build of this file fail with "unknown module prefix 'RequestProject'".
-/

def main (argv : List String) : IO UInt32 := gokujoMain argv
