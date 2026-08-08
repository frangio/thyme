module

namespace Thyme.Elab

public section

theorem pi_congr'
    {α₁ α₂ : Sort u} {β₁ : α₁ → Sort v} (β₂ : α₂ → Sort v)
    (hα : α₁ = α₂)
    (hβ : ∀ x, β₁ x = β₂ (cast hα x)) :
    ((x : α₁) → β₁ x) = ((x : α₂) → β₂ x) := by
  subst hα
  exact pi_congr hβ

theorem app_hcongr
    {α₁ α₂ : Sort u} {β₁ : α₁ → Sort v} (β₂ : α₂ → Sort v)
    {f₁ : (x : α₁) → β₁ x} {f₂ : (x : α₂) → β₂ x}
    {a₁ : α₁} {a₂ : α₂}
    (hα : α₁ = α₂)
    (hβ : ∀ x, β₁ x = β₂ (cast hα x))
    (hf : cast (pi_congr' β₂ hα hβ) f₁ = f₂)
    (ha : cast hα a₁ = a₂) :
    f₁ a₁ ≍ f₂ a₂ := by
  subst hα
  subst a₂
  have hβ' : β₁ = β₂ := funext hβ
  subst hβ'
  rw [cast_eq] at hf
  subst f₂
  rfl

theorem hfunext
    {α₁ α₂ : Sort u} {β₁ : α₁ → Sort v} (β₂ : α₂ → Sort v)
    {f₁ : (x : α₁) → β₁ x} (f₂ : (x : α₂) → β₂ x)
    (hα : α₁ = α₂)
    (h : ∀ x, f₁ x ≍ f₂ (cast hα x)) :
    f₁ ≍ f₂ := by
  subst hα
  have hβ : β₁ = β₂ := funext fun x => type_eq_of_heq (h x)
  subst hβ
  apply heq_of_eq
  funext x
  exact eq_of_heq (h x)

end

end Thyme.Elab
