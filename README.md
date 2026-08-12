# Thyme

Thyme is a Lean library for typed metaprogramming based on staging, with support for dependent types and reasoning about metaprograms.

## Examples

We can implement exponentiation as a staged function of a statically known exponent:

```lean
import Thyme
open Thyme

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

We achieve this with an encoding parameterized by an interpretation selector, in which both the object-level type and term denotations are conditional on the denotation selector, while the code generator is conditional on the generator selector:

```lean
inductive Interp where
  | den
  | gen

structure Code (i : Interp) (α : i = .den → Sort u) where
  den : (h : i = .den) → α h
  gen : i = .gen → MetaM Expr
```

From an interpretation-polymorphic `c : ∀ i, Code i α`, we can obtain both components. A meta-level function must be polymorphic as a whole, as in `∀ i, Code i α → Code i β`, so as to be usable under either interpretation, in particular without requiring denotations during code generation.

To avoid threading the selector explicitly, it is packaged in the `Staged` type class:

```lean
class Staged where
  interp : Interp
```

A declaration with a `[Staged]` parameter is therefore interpretation-polymorphic in the way required of meta-level functions.
