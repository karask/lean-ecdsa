import Lake
open Lake DSL System

/-!
Constant-time check of the compiled code with valgrind (see `README.md`).
Kept in a separate package so that the library itself has no C or valgrind
dependency.
-/

package ctgrind

require secp256k1 from ".."

lean_lib CTGrind

target shim.o pkg : FilePath := do
  let src ← inputTextFile <| pkg.dir / "c" / "ctgrind_shim.c"
  let oFile := pkg.buildDir / "c" / "ctgrind_shim.o"
  buildO oFile src #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

extern_lib ctgrindshim pkg := do
  let shim ← shim.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "ctgrindshim") #[shim]

@[default_target]
lean_exe ctgrind where
  root := `CTGrind
