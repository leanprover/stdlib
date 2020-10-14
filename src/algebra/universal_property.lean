import algebra.algebra.basic

universes u₁ u₂ u₃

class has_universal_property
  -- base ring, base space, destination algebra
  (R : Type u₁) (α : Type u₂) (A : Type u₃)
  [comm_semiring R] [semiring A] [algebra R A]
  -- the type of homomorphism to use, which must coerce to a suitable function
  -- note: what to do about universes here?
  (hom_α : Π (A₂ : Type u₃) [semiring A₂] [algebra R A₂], Type*)
  [∀ (A₂ : Type u₃) [semiring A₂] [algebra R A₂], has_coe (hom_α A₂) (α → A₂)] :=
(hom_comp {A₂ : Type*} [semiring A₂] [algebra R A₂] :
  (A →ₐ[R] A₂) → hom_α A → hom_α A₂)
(hom_comp_eq {A₂ : Type*} [semiring A₂] [algebra R A₂] :
  ∀ (f : A →ₐ[R] A₂) (g : hom_α A), (hom_comp f g : α → A₂) = f ∘ (g : α → A))
(hom_ext' {A₂ : Type*} [semiring A₂] [algebra R A₂] :
  ∀ (f g : hom_α A₂), (f : α → A₂) = (g : α → A₂) ↔ f = g)
(ι :
  hom_α A)
(lift {A₂ : Type*} [semiring A₂] [algebra R A₂] :
  hom_α A₂ → A →ₐ[R] A₂)
(lift_unique {A₂ : Type*} [semiring A₂] [algebra R A₂] (f : hom_α A₂) (g : A →ₐ[R] A₂) :
  hom_comp g ι = f ↔ g = lift f)

namespace has_universal_property

variables (R : Type u₁) (α : Type u₂) (A : Type u₃)
  [comm_semiring R] [semiring A] [algebra R A]
  (hom_α : Π (A₂ : Type u₃) [semiring A₂], by exactI Π [algebra R A₂], Type*)
  [∀ (A₂ : Type u₃) [semiring A₂], by exactI Π [algebra R A₂], by exactI has_coe (hom_α A₂) (α → A₂)]

variables {A₂ : Type u₃} [semiring A₂] [algebra R A₂] (f : hom_α A₂) (g : A →ₐ[R] A₂)

variables [has_universal_property R α A hom_α]

@[simp]
theorem lift_ι_apply (x : α) :
  (lift α f : A →ₐ[R] A₂) (((ι R α : hom_α A) : α → A) x) = (f : α → A₂) x :=
begin
  rw ←function.comp_apply (lift α f : A →ₐ[R] A₂) ((ι R α : hom_α A) : α → A) x,
  rw ←hom_comp_eq _ (ι R α),
  congr,
  rw lift_unique,
end

@[simp]
theorem ι_comp_lift :
  (lift α f : A →ₐ[R] A₂) ∘ ((ι R α : hom_α A) : α → A) = f := by { ext, simp, }

@[simp]
theorem lift_comp_ι :
  lift α (hom_comp α g (ι R α : hom_α A)) = g := by {symmetry, rw ←lift_unique}

@[ext]
theorem hom_ext {f g : A →ₐ[R] A₂}
  (w : (f : A → A₂) ∘ ((ι R α : hom_α A) : α → A) = (g : A → A₂) ∘ ((ι R α : hom_α A) : α → A)) : f = g :=
begin
  have : g = lift α (hom_comp α g (ι R α : hom_α A)), by rw ←lift_unique,
  rw [this],
  rw [←lift_unique],
  rw ←hom_ext' R A (_ : hom_α A₂) _,
  rw [hom_comp_eq, hom_comp_eq, w],
  apply_instance,
end

-- variables [add_monoid A] [add_monoid α]
-- #check (coe (sorry : α →+ A) : α → A)

-- end has_universal_property

-- #check ((→) ℕ)
-- #check ((⟶) ℕ)
