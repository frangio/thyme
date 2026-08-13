module

namespace Thyme.Prelude

scoped syntax:lead (name := codeStx) "Code " term:arg : term
scoped syntax:max (name := quoteStx) "`⟨" term "⟩" : term
scoped syntax:max (name := spliceStx) "~" term:max : term

end Thyme.Prelude
