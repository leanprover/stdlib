/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import tactic.lint
import tactic.ext

section sigma
variables {α : Type*} {β : α → Type*}

instance [inhabited α] [inhabited (β (default α))] : inhabited (sigma β) :=
⟨⟨default α, default (β (default α))⟩⟩

instance [h₁ : decidable_eq α] [h₂ : ∀a, decidable_eq (β a)] : decidable_eq (sigma β)
| ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ := match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
  | _, b₁, _, b₂, is_true (eq.refl a) :=
    match b₁, b₂, h₂ a b₁ b₂ with
    | _, _, is_true (eq.refl b) := is_true rfl
    | b₁, b₂, is_false n := is_false (assume h, sigma.no_confusion h (λe₁ e₂, n $ eq_of_heq e₂))
    end
  | a₁, _, a₂, _, is_false n := is_false (assume h, sigma.no_confusion h (λe₁ e₂, n e₁))
  end

lemma sigma_mk_injective {i : α} : function.injective (@sigma.mk α β i)
| _ _ rfl := rfl

@[simp, nolint simp_nf] -- sometimes the built-in injectivity support does not work
theorem sigma.mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
  sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ (a₁ = a₂ ∧ b₁ == b₂) :=
by simp

@[simp] theorem sigma.eta : ∀ x : Σ a, β a, sigma.mk x.1 x.2 = x
| ⟨i, x⟩ := rfl

@[ext]
lemma sigma.ext {x₀ x₁ : sigma β}
  (h₀ : x₀.1 = x₁.1)
  (h₁ : x₀.1 = x₁.1 → x₀.2 == x₁.2) :
  x₀ = x₁ :=
by casesm* sigma _; cases h₀; cases h₁ h₀; refl

@[simp] theorem sigma.forall {p : (Σ a, β a) → Prop} :
  (∀ x, p x) ↔ (∀ a b, p ⟨a, b⟩) :=
⟨assume h a b, h ⟨a, b⟩, assume h ⟨a, b⟩, h a b⟩

@[simp] theorem sigma.exists {p : (Σ a, β a) → Prop} :
  (∃ x, p x) ↔ (∃ a b, p ⟨a, b⟩) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

@[simp] theorem sigma.mk_fst (a : α) (b : β a) : (sigma.mk a b).fst = a := rfl

@[simp] theorem sigma.mk_snd (a : α) (b : β a) : (sigma.mk a b).snd = b := rfl

variables {α₁ : Type*} {α₂ : Type*} {β₁ : α₁ → Type*} {β₂ : α₂ → Type*}

/-- Map the left and right components of a sigma -/
def sigma.map (f₁ : α₁ → α₂) (f₂ : Πa, β₁ a → β₂ (f₁ a)) (x : sigma β₁) : sigma β₂ :=
⟨f₁ x.1, f₂ x.1 x.2⟩

lemma function.injective.sigma_map {f₁ : α₁ → α₂} {f₂ : Πa, β₁ a → β₂ (f₁ a)}
  (h₁ : function.injective f₁) (h₂ : ∀ a, function.injective (f₂ a)) :
  function.injective (sigma.map f₁ f₂)
| ⟨i, x⟩ ⟨j, y⟩ h :=
begin
  have : i = j, from h₁ (sigma.mk.inj_iff.mp h).1,
  subst j,
  have : x = y, from h₂ i (eq_of_heq (sigma.mk.inj_iff.mp h).2),
  subst y
end

lemma function.surjective.sigma_map {f₁ : α₁ → α₂} {f₂ : Πa, β₁ a → β₂ (f₁ a)}
  (h₁ : function.surjective f₁) (h₂ : ∀ a, function.surjective (f₂ a)) :
  function.surjective (sigma.map f₁ f₂) :=
begin
  intros y,
  cases y with j y,
  cases h₁ j with i hi,
  subst j,
  cases h₂ i y with x hx,
  subst y,
  exact ⟨⟨i, x⟩, rfl⟩
end


end sigma

section psigma
variables {α : Sort*} {β : α → Sort*}

/-- Nondependent eliminator for `psigma`. -/
def psigma.elim {γ} (f : ∀ a, β a → γ) (a : psigma β) : γ :=
psigma.cases_on a f

@[simp] theorem psigma.elim_val {γ} (f : ∀ a, β a → γ) (a b) : psigma.elim f ⟨a, b⟩ = f a b := rfl

instance [inhabited α] [inhabited (β (default α))] : inhabited (psigma β) :=
⟨⟨default α, default (β (default α))⟩⟩

instance [h₁ : decidable_eq α] [h₂ : ∀a, decidable_eq (β a)] : decidable_eq (psigma β)
| ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ := match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
  | _, b₁, _, b₂, is_true (eq.refl a) :=
    match b₁, b₂, h₂ a b₁ b₂ with
    | _, _, is_true (eq.refl b) := is_true rfl
    | b₁, b₂, is_false n := is_false (assume h, psigma.no_confusion h (λe₁ e₂, n $ eq_of_heq e₂))
    end
  | a₁, _, a₂, _, is_false n := is_false (assume h, psigma.no_confusion h (λe₁ e₂, n e₁))
  end

theorem psigma.mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
  @psigma.mk α β a₁ b₁ = @psigma.mk α β a₂ b₂ ↔ (a₁ = a₂ ∧ b₁ == b₂) :=
iff.intro psigma.mk.inj $
  assume ⟨h₁, h₂⟩, match a₁, a₂, b₁, b₂, h₁, h₂ with _, _, _, _, eq.refl a, heq.refl b := rfl end

variables {α₁ : Sort*} {α₂ : Sort*} {β₁ : α₁ → Sort*} {β₂ : α₂ → Sort*}

/-- Map the left and right components of a sigma -/
def psigma.map (f₁ : α₁ → α₂) (f₂ : Πa, β₁ a → β₂ (f₁ a)) : psigma β₁ → psigma β₂
| ⟨a, b⟩ := ⟨f₁ a, f₂ a b⟩

end psigma
