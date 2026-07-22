# TMeta

TMeta is an experimental Lean library for type-safe staged programming, supporting dependent types and reasoning about metaprograms.

In TMeta, a metaprogram for constructing a Lean expression of type `⍺` is a term of type `Code ⍺`, simultaneously carrying a code generator and a denotation of type `⍺`.

```lean
Code.gen {⍺ : Sort u} : Code ⍺ → MetaM Expr
Code.val {⍺ : Sort u} : Code ⍺ → ⍺
```

A metaprogram built with TMeta's staging primitives is coherent: the expression produced by its code generator is definitionally equal to its denotation.

The staging primitives are quotation and splicing. A quotation `` `⟨e⟩ `` builds a metaprogram of type `Code α` from an expression `e : α`. A splice `~c` allows a metaprogram `c : Code α` to be used as an expression of type `α`.

```lean
e : α       ⊢ `⟨e⟩ : Code α
c : Code α  ⊢  ~c  : α
```

A splice `~c` is denotationally `c.val`. Operationally, outside a quotation, `c`'s generator is evaluated during elaboration and its result replaces the splice. Inside a quotation, `c`'s generator is instead incorporated into that quotation's generator.

For example, we can implement exponentiation as a staged program that specializes a statically known exponent:

```lean
import TMeta
open TMeta

def exp : Nat → Code Nat → Code Nat
  | 0, _ => `⟨1⟩
  | n + 1, x => `⟨~(exp n x) * ~x⟩
```

Then `` ~(exp 3 `⟨2⟩) `` elaborates to `1 * 2 * 2 * 2`.

More interestingly, the base need not be a closed expression, so we can define:

```lean
def exp3 (x : Nat) : Nat :=
  ~(exp 3 `⟨x⟩)
```

The body of `exp3` elaborates to `1 * x * x * x`.

We can reason about `exp` in terms of its denotation:

```lean
theorem exp_eq_pow (n : Nat) (x : Code Nat) :
    (exp n x).val = x.val ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.pow_succ, exp, ih]
```

By coherence, theorems about the denotation of metaprograms produced by `exp` transfer to their generated code.

We can conveniently make use of coherence in a `@[csimp]` theorem to retain a compositional definition for proofs while directing the compiler to use an efficient generated implementation for compiled execution:

```lean
def exp3 (x : Nat) : Nat :=
  (exp 3 (.quote x)).val

def exp3.staged (x : Nat) : Nat :=
  ~(exp 3 `⟨x⟩)

@[csimp]
theorem exp3.eq_staged : exp3 = exp3.staged :=
  rfl
```

Note that one definition uses staging syntax while the other uses the staging primitives as functions. The former not only ensures coherence but also performs a stage checking validation that rejects invalid cross-stage references, as a prerequisite to turning a staged expression into a code generator. As an example, `` `⟨fun x => ~x⟩ `` is not a valid staged program, because `x` is bound inside a quotation and dereferenced in a splice that escapes it. In `exp3`, we want to opt out of stage checking and do not care about coherence (`.quote x : Code Nat` isn't), as they are not relevant for and may get in the way of reasoning.

## Design and implementation

TMeta is based on András Kovács's [*Staged Compilation with Two-Level Type Theory*](https://dl.acm.org/doi/10.1145/3547641), extended to arbitrarily nested stages. Unlike the calculus presented there, TMeta uses Lean's ordinary universes at every stage. Of the two inverse laws, only `` ~`⟨e⟩ = e `` holds definitionally, while `` `⟨~c⟩ = c `` holds propositionally.

The definition of `Code` is basically:

```lean
structure Code (α : Sort u) : Sort (max 1 u) where
  get : Unit → α
  xfc : False → MetaM Expr
```

`xfc` stands for *ex falso code generator*. Recall that quotations may be nested and that inner quotations may refer to variables bound in enclosing ones. During code generation, these variables are available as syntax, but not as values of their Lean types. The transformation must nevertheless construct `Code α` terms for nested quotations, since they may be passed to ordinary functions. Under a local assumption of `False`, it therefore supplies the denotational component by ex falso. The `get` field is thunked so that this placeholder is never evaluated merely by constructing the `Code` term. Crucially, no proof of `False` appears in kernel-facing terms, and this mechanism introduces no additional axioms.
