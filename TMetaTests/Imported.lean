module

public import TMeta

open TMeta

public section

@[expose]
def importedSucc (x : Code Nat) : Code Nat :=
  `⟨~x + 1⟩

/-- A non-exposed definition used to test coherence diagnostics across module boundaries. -/
def opaqueImportedSucc (x : Code Nat) : Code Nat :=
  `⟨~x + 1⟩

end
