# Staging Rules

## Syntax

```text
i ∈ ℕ

Γ ::= · | Γ, x :ᵢ α
```

The judgment

```text
Γ ⊢ t :ᵢ α
```

means that `t` has type `α` at quotation depth `i`.

## Staged Typing

### Core Expressions

```text
       x :ᵢ α ∈ Γ
──────────────────────── VAR
       Γ ⊢ x :ᵢ α


       c : α ∈ E
──────────────────────── CONST
       Γ ⊢ c :ᵢ α

  Γ ⊢ f :ᵢ (x : α) → β    Γ ⊢ a :ᵢ α
────────────────────────────────────────────── APP
         Γ ⊢ f a :ᵢ β[x ↦ a]


  Γ ⊢ α :ᵢ Sort u    Γ, x :ᵢ α ⊢ t :ᵢ β
──────────────────────────────────────────────── LAM
  Γ ⊢ (fun (x : α) => t) :ᵢ (x : α) → β


  Γ ⊢ t :ᵢ α    Γ ⊢ α ≡ β : Sort u
───────────────────────────────────────── CONV
             Γ ⊢ t :ᵢ β
```

### Lifting Expressions

```text
       Γ ⊢ α :ᵢ₊₁ Sort u
──────────────────────────── LIFT
  Γ ⊢ ⇑α :ᵢ Sort (max 1 u)


       Γ ⊢ t :ᵢ₊₁ α
──────────────────────── QUOTE
      Γ ⊢ ⟨t⟩ :ᵢ ⇑α


       Γ ⊢ t :ᵢ ⇑α
──────────────────────── SPLICE
      Γ ⊢ ∼t :ᵢ₊₁ α
```

## Equality

```text
       Γ ⊢ t :ᵢ₊₁ α
──────────────────────────────── SPLICE-QUOTE
       Γ ⊢ ∼⟨t⟩ ≡ t :ᵢ₊₁ α


       Γ ⊢ t :ᵢ ⇑α
──────────────────────────────── QUOTE-SPLICE
      Γ ⊢ ⟨∼t⟩ ≡ t :ᵢ ⇑α
```
