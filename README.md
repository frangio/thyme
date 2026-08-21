# Thyme

Thyme is a Lean library for typed metaprogramming based on staging, with support for dependent types and reasoning about metaprograms.

## Installation

```toml
# lakefile.toml
[[require]]
name = "thyme"
git = "https://github.com/frangio/thyme"
```

```lean
import Thyme
open Thyme.Prelude
```

## Core concepts

`Code α` is the type of metaprograms that generate terms of type `α`.

If `e : α`, the quotation `` `⟨e⟩ : Code α `` constructs a metaprogram that generates the term `e`, with any splices in `e` evaluated as described next.

If `c : Code α`, the splice `~c : α` runs `c`'s code generator and inserts the result in its place. Inside a quotation, the splice is evaluated as part of that quotation's code generator. Outside a quotation, it is evaluated immediately during elaboration.

Declarations that produce metaprograms or metaprogram types must have an instance parameter `[Staged]` if they are meant to be used for code generation. The parameter may be omitted if the declaration is used for reasoning only.

## Examples

We can implement exponentiation as a staged function of a statically known exponent:

```lean
import Thyme
open Thyme.Prelude

def exp [Staged] (x : Code Nat) : Nat → Code Nat
  | 0 => `⟨1⟩
  | n + 1 => `⟨~(exp x n) * ~x⟩
```

Then `` ~(exp `⟨2⟩ 3) `` elaborates to `1 * 2 * 2 * 2`.

More interestingly, the code for `x` can refer to bound variables in context:

```lean
def exp3 (x : Nat) : Nat :=
  ~(exp `⟨x⟩ 3)
```

The body of `exp3` is then `1 * x * x * x`.

We can reason about the denotation of metaprograms through `Code.den`:

```lean
theorem exp_eq_pow : (exp x n).den = x.den ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih, exp, Nat.pow_succ]
```

Coherent metaprograms generate code that is definitionally equal to their denotation, and properties carry over:

```lean
theorem exp3_coherent : exp3 x = (exp `⟨x⟩ 3).den :=
  rfl

theorem exp3_eq_pow3 : exp3 x = x ^ 3 :=
  exp_eq_pow ▸ exp3_coherent
```

Thyme's staging syntax constructs coherent metaprograms, but an arbitrary `Code α` value is not intrinsically coherent.

Metaprograms can be dependently typed and produce proof terms:

```lean
def zero_mul [Staged] (x y : Code Nat) (h : Code (~x = 0 * ~y)) : Code (~x = 0) :=
  `⟨by simpa using ~h⟩
```

## Design and implementation

Thyme implements a staging type system inspired by András Kovács's [*Staged Compilation with Two-Level Type Theory*](https://dl.acm.org/doi/10.1145/3547641). Our implementation must account for two components of a metaprogram: a denotational component given by a Lean term of the object-level type, and a code generator given by a `MetaM Expr` action. A simple representation as a product of these components is not viable, however, because the denotation of an open object-level term is not available during code generation. For example, to elaborate the term ``fun (x : α) => ~(f `⟨x⟩)``, the function `f` must be invoked with a `Code α` whose code generator produces a reference to `x`, at a point where no actual value of type `α` is available. Dropping metaprogram denotations altogether would avoid this difficulty, at the cost of introducing separate machinery to represent and check object-level types. Having denotations allows the typing rule for splicing to be realized directly in Lean: a splice of `c : Code α` can be elaborated as its denotation, an ordinary Lean term of type `α`, and Thyme can therefore rely on Lean itself to check object-level types and terms. The encoding must make denotations available for this purpose without requiring them during code generation.

We achieve this with an encoding parameterized by an abstract staging context with denotational and generative capabilities that are mutually exclusive. The object-level type and term denotations are conditional on the denotational capability, while the code generator is conditional on the generative capability:

```lean
class Staged where
  Den : Prop

def Staged.Gen [s : Staged] : Prop := ¬s.Den

structure Code [s : Staged] (α : s.Den → Sort u) where
  den : (h : s.Den) → α h
  gen : s.Gen → MetaM Expr
```

The canonical staging contexts for the two capabilities are then:

```lean
def Staged.den : Staged := ⟨True⟩
def Staged.gen : Staged := ⟨False⟩
```

From a metaprogram `c : ∀ [Staged], Code α` polymorphic in the staging capabilities we can obtain either component by instantiating `c` with the denotational or generative context. Such a value can be viewed as a pair of a denotation and a code generator. Crucially, a meta-level function must be polymorphic in the capabilities as a whole, as in `∀ [Staged], Code α → Code β`, rather than receiving a capability-polymorphic `Code` argument. When instantiated generatively, the function therefore cannot require the denotation of its input.
