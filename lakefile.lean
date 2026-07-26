import Lake

open System Lake DSL

package tmeta where
  testDriver := "TMetaTests"
  version := v!"0.1.0"
  description := "Type-safe staged programming supporting dependent types and reasoning about metaprograms."
  license := "Apache-2.0"
  leanOptions := #[⟨`backward.do.legacy, true⟩]

input_file runtime.c where
  path := "runtime.c"
  text := true

target runtime.o pkg : FilePath := do
  let src ← runtime.c.fetch
  let output := pkg.buildDir / "runtime.o"
  buildLeanO output src #[] #["-fPIC"]

@[default_target]
lean_lib TMeta where
  precompileModules := true
  moreLinkObjs := #[runtime.o]

lean_lib TMetaTests
