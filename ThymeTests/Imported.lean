module

public import Thyme

open Thyme.Prelude

public section

@[expose]
def importedSucc [Staged] (x : Code Nat) : Code Nat :=
  `⟨~x + 1⟩

/-- A non-exposed definition used to test coherence diagnostics across module boundaries. -/
def opaqueImportedSucc [Staged] (x : Code Nat) : Code Nat :=
  `⟨~x + 1⟩

end
