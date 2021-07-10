/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

# Preorder homomorphisms

Bundled monotone functions, `x ≤ y → f x ≤ f y`.
-/
import logic.function.iterate
import order.basic
import order.bounded_lattice
import order.complete_lattice
import tactic.monotonicity

/-! # Category of preorders -/

/-- Bundled monotone (aka, increasing) function -/
structure preorder_hom (α β : Type*) [preorder α] [preorder β] :=
(to_fun   : α → β)
(monotone' : monotone to_fun)

infixr ` →ₘ `:25 := preorder_hom

namespace preorder_hom
variables {α : Type*} {β : Type*} {γ : Type*} [preorder α] [preorder β] [preorder γ]

instance : has_coe_to_fun (preorder_hom α β) :=
{ F := λ f, α → β,
  coe := preorder_hom.to_fun }

initialize_simps_projections preorder_hom (to_fun → coe)

@[mono]
lemma monotone (f : α →ₘ β) : monotone f :=
preorder_hom.monotone' f

@[simp] lemma to_fun_eq_coe {f : α →ₘ β} : f.to_fun = f := rfl
@[simp] lemma coe_fun_mk {f : α → β} (hf : _root_.monotone f) : (mk f hf : α → β) = f := rfl

@[ext] -- See library note [partially-applied ext lemmas]
lemma ext (f g : preorder_hom α β) (h : (f : α → β) = g) : f = g :=
by { cases f, cases g, congr, exact h }

/-- The identity function as bundled monotone function. -/
@[simps {fully_applied := ff}]
def id : preorder_hom α α :=
⟨id, monotone_id⟩

instance : inhabited (preorder_hom α α) := ⟨id⟩

/-- The composition of two bundled monotone functions. -/
@[simps {fully_applied := ff}]
def comp (g : preorder_hom β γ) (f : preorder_hom α β) : preorder_hom α γ :=
⟨g ∘ f, g.monotone.comp f.monotone⟩

@[simp] lemma comp_id (f : preorder_hom α β) : f.comp id = f :=
by { ext, refl }

@[simp] lemma id_comp (f : preorder_hom α β) : id.comp f = f :=
by { ext, refl }

/-- `subtype.val` as a bundled monotone function.  -/
@[simps {fully_applied := ff}]
def subtype.val (p : α → Prop) : subtype p →ₘ α :=
⟨subtype.val, λ x y h, h⟩

-- TODO[gh-6025]: make this a global instance once safe to do so
/-- There is a unique monotone map from a subsingleton to itself. -/
local attribute [instance]
def unique [subsingleton α] : unique (α →ₘ α) :=
{ default := preorder_hom.id, uniq := λ a, ext _ _ (subsingleton.elim _ _) }

lemma preorder_hom_eq_id [subsingleton α] (g : α →ₘ α) : g = preorder_hom.id :=
subsingleton.elim _ _

/-- The preorder structure of `α →ₘ β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ g a`. -/
instance : preorder (α →ₘ β) :=
preorder.lift preorder_hom.to_fun

instance {β : Type*} [partial_order β] : partial_order (α →ₘ β) :=
partial_order.lift preorder_hom.to_fun $ by rintro ⟨⟩ ⟨⟩ h; congr; exact h

@[simps]
instance {β : Type*} [semilattice_sup β] : has_sup (α →ₘ β) :=
{ sup := λ f g, ⟨λ a, f a ⊔ g a, λ x y h, sup_le_sup (f.monotone h) (g.monotone h)⟩ }

instance {β : Type*} [semilattice_sup β] : semilattice_sup (α →ₘ β) :=
{ sup := has_sup.sup,
  le_sup_left := λ a b x, le_sup_left,
  le_sup_right := λ a b x, le_sup_right,
  sup_le := λ a b c h₀ h₁ x, sup_le (h₀ x) (h₁ x),
  .. (_ : partial_order (α →ₘ β)) }

@[simps]
instance {β : Type*} [semilattice_inf β] : has_inf (α →ₘ β) :=
{ inf := λ f g, ⟨λ a, f a ⊓ g a, λ x y h, inf_le_inf (f.monotone h) (g.monotone h)⟩ }

instance {β : Type*} [semilattice_inf β] : semilattice_inf (α →ₘ β) :=
{ inf := (⊓),
  inf_le_left := λ a b x, inf_le_left,
  inf_le_right := λ a b x, inf_le_right,
  le_inf := λ a b c h₀ h₁ x, le_inf (h₀ x) (h₁ x),
  .. (_ : partial_order (α →ₘ β)) }

instance {β : Type*} [lattice β] : lattice (α →ₘ β) :=
{ .. (_ : semilattice_sup (α →ₘ β)),
  .. (_ : semilattice_inf (α →ₘ β)) }

@[simps]
instance {β : Type*} [order_bot β] : has_bot (α →ₘ β) :=
{ bot := ⟨λ a, ⊥, λ a b h, le_refl _⟩ }

instance {β : Type*} [order_bot β] : order_bot (α →ₘ β) :=
{ bot := ⊥,
  bot_le := λ a x, bot_le,
  .. (_ : partial_order (α →ₘ β)) }

@[simps]
instance {β : Type*} [order_top β] : has_top (α →ₘ β) :=
{ top := ⟨λ a, ⊤, λ a b h, le_refl _⟩ }

instance {β : Type*} [order_top β] : order_top (α →ₘ β) :=
{ top := ⊤,
  le_top := λ a x, le_top,
  .. (_ : partial_order (α →ₘ β)) }

@[simps]
instance {β : Type*} [complete_lattice β] : has_Inf (α →ₘ β) :=
{ Inf := λ s, ⟨ λ x, Inf ((λ f : _ →ₘ _, f x) '' s), λ x y h,
    Inf_le_Inf_of_forall_exists_le begin
      simp only [and_imp, exists_prop, set.mem_image, exists_exists_and_eq_and, exists_imp_distrib],
      intros,
      subst_vars,
      refine ⟨_,by assumption, monotone _ h⟩
    end ⟩ }

@[simps]
instance {β : Type*} [complete_lattice β] : has_Sup (α →ₘ β) :=
{ Sup := λ s, ⟨ λ x, Sup ((λ f : _ →ₘ _, f x) '' s), λ x y h,
    Sup_le_Sup_of_forall_exists_le begin
      simp only [and_imp, exists_prop, set.mem_image, exists_exists_and_eq_and, exists_imp_distrib],
      intros,
      subst_vars,
      refine ⟨_,by assumption, monotone _ h⟩
    end ⟩ }

@[simps Sup Inf]
instance {β : Type*} [complete_lattice β] : complete_lattice (α →ₘ β) :=
{ Sup := has_Sup.Sup,
  le_Sup := λ s f hf x, @le_Sup β _ ((λ f : _ →ₘ _, f x) '' s) (f x) ⟨f, hf, rfl⟩,
  Sup_le := λ s f hf x, @Sup_le β _ _ _ $ λ b (h : b ∈ (λ (f : α →ₘ β), f x) '' s),
              by rcases h with ⟨g, h, ⟨ ⟩⟩; apply hf _ h,
  Inf := has_Inf.Inf,
  le_Inf := λ s f hf x, @le_Inf β _ _ _ $ λ b (h : b ∈ (λ (f : α →ₘ β), f x) '' s),
              by rcases h with ⟨g, h, ⟨ ⟩⟩; apply hf _ h,
  Inf_le := λ s f hf x, @Inf_le β _ ((λ f : _ →ₘ _, f x) '' s) (f x) ⟨f, hf, rfl⟩,
  .. (_ : lattice (α →ₘ β)),
  .. (_ : order_top (α →ₘ β)),
  .. (_ : order_bot (α →ₘ β)) }

lemma iterate_sup_le_sup_iff {α : Type*} [semilattice_sup α] (f : α →ₘ α) :
  (∀ n₁ n₂ a₁ a₂, f^[n₁ + n₂] (a₁ ⊔ a₂) ≤ (f^[n₁] a₁) ⊔ (f^[n₂] a₂)) ↔
  (∀ a₁ a₂, f (a₁ ⊔ a₂) ≤ (f a₁) ⊔ a₂) :=
begin
  split; intros h,
  { exact h 1 0, },
  { intros n₁ n₂ a₁ a₂, have h' : ∀ n a₁ a₂, f^[n] (a₁ ⊔ a₂) ≤ (f^[n] a₁) ⊔ a₂,
    { intros n, induction n with n ih; intros a₁ a₂,
      { refl, },
      { calc f^[n + 1] (a₁ ⊔ a₂) = (f^[n] (f (a₁ ⊔ a₂))) : function.iterate_succ_apply f n _
                             ... ≤ (f^[n] ((f a₁) ⊔ a₂)) : f.monotone.iterate n (h a₁ a₂)
                             ... ≤ (f^[n] (f a₁)) ⊔ a₂ : ih _ _
                             ... = (f^[n + 1] a₁) ⊔ a₂ : by rw ← function.iterate_succ_apply, }, },
    calc f^[n₁ + n₂] (a₁ ⊔ a₂) = (f^[n₁] (f^[n₂] (a₁ ⊔ a₂))) : function.iterate_add_apply f n₁ n₂ _
                           ... = (f^[n₁] (f^[n₂] (a₂ ⊔ a₁))) : by rw sup_comm
                           ... ≤ (f^[n₁] ((f^[n₂] a₂) ⊔ a₁)) : f.monotone.iterate n₁ (h' n₂ _ _)
                           ... = (f^[n₁] (a₁ ⊔ (f^[n₂] a₂))) : by rw sup_comm
                           ... ≤ (f^[n₁] a₁) ⊔ (f^[n₂] a₂) : h' n₁ a₁ _, },
end

end preorder_hom

namespace order_embedding

/-- Convert an `order_embedding` to a `preorder_hom`. -/
@[simps {fully_applied := ff}]
def to_preorder_hom {X Y : Type*} [preorder X] [preorder Y] (f : X ↪o Y) : X →ₘ Y :=
{ to_fun := f,
  monotone' := f.monotone }

end order_embedding
section rel_hom

variables {α β : Type*} [partial_order α] [preorder β]

namespace rel_hom

variables (f : ((<) : α → α → Prop) →r ((<) : β → β → Prop))

/-- A bundled expression of the fact that a map between partial orders that is strictly monotonic
is weakly monotonic. -/
@[simps {fully_applied := ff}]
def to_preorder_hom : α →ₘ β :=
{ to_fun    := f,
  monotone' := strict_mono.monotone (λ x y, f.map_rel), }

end rel_hom

lemma rel_embedding.to_preorder_hom_injective (f : ((<) : α → α → Prop) ↪r ((<) : β → β → Prop)) :
  function.injective (f : ((<) : α → α → Prop) →r ((<) : β → β → Prop)).to_preorder_hom :=
λ _ _ h, f.injective h

end rel_hom
