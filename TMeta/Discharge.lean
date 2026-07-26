module

namespace TMeta

@[extern "tmeta_panic_thunk", never_extract]
unsafe def panicThunk {α : Sort u} (_message : @& String) (_ : Unit) : α :=
  lcUnreachable

@[always_inline]
unsafe def discharge!Impl {α : Sort u} {β : Sort v} [Inhabited β]
    (k : (Unit → α) → β) (msg := "a discharged thunk was forced") : β :=
  k (panicThunk msg)

@[implemented_by discharge!Impl]
public opaque discharge! {α : Sort u} {β : Sort v} [Inhabited β]
    (k : (Unit → α) → β) (msg := "a discharged thunk was forced") : β

end TMeta
