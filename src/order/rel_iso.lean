/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import logic.embedding
import order.rel_classes
import data.set.intervals.basic
import order.directed

open function

universes u v w
variables {α : Type*} {β : Type*} {γ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
@[nolint has_inhabited_instance]
structure rel_hom {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) :=
(to_fun : α → β)
(map_rel' : ∀ {a b}, r a b → s (to_fun a) (to_fun b))

infix ` →r `:25 := rel_hom

namespace rel_hom

instance : has_coe_to_fun (r →r s) := ⟨λ _, α → β, λ o, o.to_fun⟩

initialize_simps_projections rel_hom (to_fun → apply)

theorem map_rel (f : r →r s) : ∀ {a b}, r a b → s (f a) (f b) := f.map_rel'

@[simp] theorem coe_fn_mk (f : α → β) (o) :
  (@rel_hom.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_fun (f : r →r s) : (f.to_fun : α → β) = f := rfl

/-- The map `coe_fn : (r →r s) → (α → β)` is injective. We can't use `function.injective`
here but mimic its signature by using `⦃e₁ e₂⦄`. -/
theorem coe_fn_inj : ∀ ⦃e₁ e₂ : r →r s⦄, (e₁ : α → β) = e₂ → e₁ = e₂
| ⟨f₁, o₁⟩ ⟨f₂, o₂⟩ h := by { congr, exact h }

@[ext] theorem ext ⦃f g : r →r s⦄ (h : ∀ x, f x = g x) : f = g :=
coe_fn_inj (funext h)

theorem ext_iff {f g : r →r s} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

/-- Identity map is a relation homomorphism. -/
@[refl, simps] protected def id (r : α → α → Prop) : r →r r :=
⟨λ x, x, λ a b x, x⟩

/-- Composition of two relation homomorphisms is a relation homomorphism. -/
@[trans, simps] protected def comp (g : s →r t) (f : r →r s) : r →r t :=
⟨λ x, g (f x), λ a b h, g.2 (f.2 h)⟩

/-- A relation homomorphism is also a relation homomorphism between dual relations. -/
protected def swap (f : r →r s) : swap r →r swap s :=
⟨f, λ a b, f.map_rel⟩

/-- A function is a relation homomorphism from the preimage relation of `s` to `s`. -/
def preimage (f : α → β) (s : β → β → Prop) : f ⁻¹'o s →r s := ⟨f, λ a b, id⟩

protected theorem is_irrefl : ∀ (f : r →r s) [is_irrefl β s], is_irrefl α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a h, H _ (o h)⟩

protected theorem is_asymm : ∀ (f : r →r s) [is_asymm β s], is_asymm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h₁ h₂, H _ _ (o h₁) (o h₂)⟩

protected theorem acc (f : r →r s) (a : α) : acc s (f a) → acc r a :=
begin
  generalize h : f a = b, intro ac,
  induction ac with _ H IH generalizing a, subst h,
  exact ⟨_, λ a' h, IH (f a') (f.map_rel h) _ rfl⟩
end

protected theorem well_founded : ∀ (f : r →r s) (h : well_founded s), well_founded r
| f ⟨H⟩ := ⟨λ a, f.acc _ (H _)⟩

lemma map_inf {α β : Type*} [semilattice_inf α] [linear_order β]
  (a : ((<) : β → β → Prop) →r ((<) : α → α → Prop)) (m n : β) : a (m ⊓ n) = a m ⊓ a n :=
begin
  symmetry, cases le_or_lt n m with h,
  { rw [inf_eq_right.mpr h, inf_eq_right], exact strict_mono.monotone (λ x y, a.map_rel) h, },
  { rw [inf_eq_left.mpr (le_of_lt h), inf_eq_left], exact le_of_lt (a.map_rel h), },
end

lemma map_sup {α β : Type*} [semilattice_sup α] [linear_order β]
  (a : ((>) : β → β → Prop) →r ((>) : α → α → Prop)) (m n : β) : a (m ⊔ n) = a m ⊔ a n :=
begin
  symmetry, cases le_or_lt m n with h,
  { rw [sup_eq_right.mpr h, sup_eq_right], exact strict_mono.monotone (λ x y, a.swap.map_rel) h, },
  { rw [sup_eq_left.mpr (le_of_lt h), sup_eq_left], exact le_of_lt (a.map_rel h), },
end

lemma directed [directed_order α] (f : ((≤) : α → α → Prop) →r s) : directed s f :=
directed_of_sup $ λ _ _, f.map_rel

end rel_hom

/-- An increasing function is injective -/
lemma injective_of_increasing (r : α → α → Prop) (s : β → β → Prop) [is_trichotomous α r]
  [is_irrefl β s] (f : α → β) (hf : ∀{x y}, r x y → s (f x) (f y)) : injective f :=
begin
  intros x y hxy,
  rcases trichotomous_of r x y with h | h | h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this,
  exact h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this
end

/-- An increasing function is injective -/
lemma rel_hom.injective_of_increasing [is_trichotomous α r]
  [is_irrefl β s] (f : r →r s) : injective f :=
injective_of_increasing r s f (λ x y, f.map_rel)

theorem surjective.well_founded_iff {f : α → β} (hf : surjective f)
  (o : ∀ {a b}, r a b ↔ s (f a) (f b)) : well_founded r ↔ well_founded s :=
iff.intro (begin
  apply rel_hom.well_founded,
  refine rel_hom.mk _ _,
  {exact classical.some hf.has_right_inverse},
  intros a b h, apply o.2, convert h,
  iterate 2 { apply classical.some_spec hf.has_right_inverse },
end) (rel_hom.well_founded ⟨f, λ _ _, o.1⟩)

/-- A relation embedding with respect to a given pair of relations `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`. -/
structure rel_embedding {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ↪ β :=
(map_rel_iff' : ∀ {a b}, s (to_embedding a) (to_embedding b) ↔ r a b)

infix ` ↪r `:25 := rel_embedding

/-- An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `rel_embedding (≤) (≤)`. -/
abbreviation order_embedding (α β : Type*) [has_le α] [has_le β] :=
@rel_embedding α β (≤) (≤)

infix ` ↪o `:25 := order_embedding

/-- The induced relation on a subtype is an embedding under the natural inclusion. -/
definition subtype.rel_embedding {X : Type*} (r : X → X → Prop) (p : X → Prop) :
  ((subtype.val : subtype p → X) ⁻¹'o r) ↪r r :=
⟨embedding.subtype p, λ x y, iff.rfl⟩

theorem preimage_equivalence {α β} (f : α → β) {s : β → β → Prop}
  (hs : equivalence s) : equivalence (f ⁻¹'o s) :=
⟨λ a, hs.1 _, λ a b h, hs.2.1 h, λ a b c h₁ h₂, hs.2.2 h₁ h₂⟩

namespace rel_embedding

/-- A relation embedding is also a relation homomorphism -/
def to_rel_hom (f : r ↪r s) : (r →r s) :=
{ to_fun := f.to_embedding.to_fun,
  map_rel' := λ x y, (map_rel_iff' f).mpr }

instance : has_coe (r ↪r s) (r →r s) := ⟨to_rel_hom⟩
-- see Note [function coercion]
instance : has_coe_to_fun (r ↪r s) := ⟨λ _, α → β, λ o, o.to_embedding⟩

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : r ↪r s) : α → β := h

initialize_simps_projections rel_embedding (to_embedding_to_fun → apply, -to_embedding)

@[simp] lemma to_rel_hom_eq_coe (f : r ↪r s) : f.to_rel_hom = f := rfl

@[simp] lemma coe_coe_fn (f : r ↪r s) : ((f : r →r s) : α → β) = f := rfl

theorem injective (f : r ↪r s) : injective f := f.inj'

theorem map_rel_iff (f : r ↪r s) : ∀ {a b}, s (f a) (f b) ↔ r a b := f.map_rel_iff'

@[simp] theorem coe_fn_mk (f : α ↪ β) (o) :
  (@rel_embedding.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_embedding (f : r ↪r s) : (f.to_embedding : α → β) = f := rfl

/-- The map `coe_fn : (r ↪r s) → (α → β)` is injective. We can't use `function.injective`
here but mimic its signature by using `⦃e₁ e₂⦄`. -/
theorem coe_fn_inj : ∀ ⦃e₁ e₂ : r ↪r s⦄, (e₁ : α → β) = e₂ → e₁ = e₂
| ⟨⟨f₁, h₁⟩, o₁⟩ ⟨⟨f₂, h₂⟩, o₂⟩ h := by { congr, exact h }

@[ext] theorem ext ⦃f g : r ↪r s⦄ (h : ∀ x, f x = g x) : f = g :=
coe_fn_inj (funext h)

theorem ext_iff {f g : r ↪r s} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

/-- Identity map is a relation embedding. -/
@[refl, simps] protected def refl (r : α → α → Prop) : r ↪r r :=
⟨embedding.refl _, λ a b, iff.rfl⟩

/-- Composition of two relation embeddings is a relation embedding. -/
@[trans] protected def trans (f : r ↪r s) (g : s ↪r t) : r ↪r t :=
⟨f.1.trans g.1, λ a b, by simp [f.map_rel_iff, g.map_rel_iff]⟩

instance (r : α → α → Prop) : inhabited (r ↪r r) := ⟨rel_embedding.refl _⟩

theorem trans_apply (f : r ↪r s) (g : s ↪r t) (a : α) : (f.trans g) a = g (f a) := rfl

@[simp] theorem coe_trans (f : r ↪r s) (g : s ↪r t) : ⇑(f.trans g) = g ∘ f := rfl

/-- A relation embedding is also a relation embedding between dual relations. -/
protected def swap (f : r ↪r s) : swap r ↪r swap s :=
⟨f.to_embedding, λ a b, f.map_rel_iff⟩

/-- If `f` is injective, then it is a relation embedding from the
  preimage relation of `s` to `s`. -/
def preimage (f : α ↪ β) (s : β → β → Prop) : f ⁻¹'o s ↪r s := ⟨f, λ a b, iff.rfl⟩

theorem eq_preimage (f : r ↪r s) : r = f ⁻¹'o s :=
by { ext a b, exact f.map_rel_iff.symm }

protected theorem is_irrefl (f : r ↪r s) [is_irrefl β s] : is_irrefl α r :=
⟨λ a, mt f.map_rel_iff.2 (irrefl (f a))⟩

protected theorem is_refl (f : r ↪r s) [is_refl β s] : is_refl α r :=
⟨λ a, f.map_rel_iff.1 $ refl _⟩

protected theorem is_symm (f : r ↪r s) [is_symm β s] : is_symm α r :=
⟨λ a b, imp_imp_imp f.map_rel_iff.2 f.map_rel_iff.1 symm⟩

protected theorem is_asymm (f : r ↪r s) [is_asymm β s] : is_asymm α r :=
⟨λ a b h₁ h₂, asymm (f.map_rel_iff.2 h₁) (f.map_rel_iff.2 h₂)⟩

protected theorem is_antisymm : ∀ (f : r ↪r s) [is_antisymm β s], is_antisymm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h₁ h₂, f.inj' (H _ _ (o.2 h₁) (o.2 h₂))⟩

protected theorem is_trans : ∀ (f : r ↪r s) [is_trans β s], is_trans α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b c h₁ h₂, o.1 (H _ _ _ (o.2 h₁) (o.2 h₂))⟩

protected theorem is_total : ∀ (f : r ↪r s) [is_total β s], is_total α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o o).1 (H _ _)⟩

protected theorem is_preorder : ∀ (f : r ↪r s) [is_preorder β s], is_preorder α r
| f H := by exactI {..f.is_refl, ..f.is_trans}

protected theorem is_partial_order : ∀ (f : r ↪r s) [is_partial_order β s], is_partial_order α r
| f H := by exactI {..f.is_preorder, ..f.is_antisymm}

protected theorem is_linear_order : ∀ (f : r ↪r s) [is_linear_order β s], is_linear_order α r
| f H := by exactI {..f.is_partial_order, ..f.is_total}

protected theorem is_strict_order : ∀ (f : r ↪r s) [is_strict_order β s], is_strict_order α r
| f H := by exactI {..f.is_irrefl, ..f.is_trans}

protected theorem is_trichotomous : ∀ (f : r ↪r s) [is_trichotomous β s], is_trichotomous α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o (or_congr f.inj'.eq_iff o)).1 (H _ _)⟩

protected theorem is_strict_total_order' :
  ∀ (f : r ↪r s) [is_strict_total_order' β s], is_strict_total_order' α r
| f H := by exactI {..f.is_trichotomous, ..f.is_strict_order}

protected theorem acc (f : r ↪r s) (a : α) : acc s (f a) → acc r a :=
begin
  generalize h : f a = b, intro ac,
  induction ac with _ H IH generalizing a, subst h,
  exact ⟨_, λ a' h, IH (f a') (f.map_rel_iff.2 h) _ rfl⟩
end

protected theorem well_founded : ∀ (f : r ↪r s) (h : well_founded s), well_founded r
| f ⟨H⟩ := ⟨λ a, f.acc _ (H _)⟩

protected theorem is_well_order : ∀ (f : r ↪r s) [is_well_order β s], is_well_order α r
| f H := by exactI {wf := f.well_founded H.wf, ..f.is_strict_total_order'}

/--
To define an relation embedding from an antisymmetric relation `r` to a reflexive relation `s` it
suffices to give a function together with a proof that it satisfies `s (f a) (f b) ↔ r a b`.
-/
def of_map_rel_iff (f : α → β) [is_antisymm α r] [is_refl β s]
  (hf : ∀ a b, s (f a) (f b) ↔ r a b) : r ↪r s :=
{ to_fun := f,
  inj' := λ x y h, antisymm ((hf _ _).1 (h ▸ refl _)) ((hf _ _).1 (h ▸ refl _)),
  map_rel_iff' := hf }

@[simp]
lemma of_map_rel_iff_coe (f : α → β) [is_antisymm α r] [is_refl β s]
  (hf : ∀ a b, s (f a) (f b) ↔ r a b) :
  ⇑(of_map_rel_iff f hf : r ↪r s) = f :=
rfl

/-- It suffices to prove `f` is monotone between strict relations
  to show it is a relation embedding. -/
def of_monotone [is_trichotomous α r] [is_asymm β s] (f : α → β)
  (H : ∀ a b, r a b → s (f a) (f b)) : r ↪r s :=
begin
  haveI := @is_asymm.is_irrefl β s _,
  refine ⟨⟨f, λ a b e, _⟩, λ a b, ⟨λ h, _, H _ _⟩⟩,
  { refine ((@trichotomous _ r _ a b).resolve_left _).resolve_right _;
    exact λ h, @irrefl _ s _ _ (by simpa [e] using H _ _ h) },
  { refine (@trichotomous _ r _ a b).resolve_right (or.rec (λ e, _) (λ h', _)),
    { subst e, exact irrefl _ h },
    { exact asymm (H _ _ h') h } }
end

@[simp] theorem of_monotone_coe [is_trichotomous α r] [is_asymm β s] (f : α → β) (H) :
  (@of_monotone _ _ r s _ _ f H : α → β) = f := rfl

/-- Embeddings of partial orders that preserve `<` also preserve `≤`  -/
def order_embedding_of_lt_embedding [partial_order α] [partial_order β]
  (f : ((<) : α → α → Prop) ↪r ((<) : β → β → Prop)) :
  α ↪o β :=
{ map_rel_iff' := by { intros, simp [le_iff_lt_or_eq,f.map_rel_iff, f.injective.eq_iff] }, .. f }

@[simp]
lemma order_embedding_of_lt_embedding_apply [partial_order α] [partial_order β]
  {f : ((<) : α → α → Prop) ↪r ((<) : β → β → Prop)} {x : α} :
  order_embedding_of_lt_embedding f x = f x := rfl

end rel_embedding

namespace order_embedding

variables [preorder α] [preorder β] (f : α ↪o β)

/-- lt is preserved by order embeddings of preorders -/
def lt_embedding : ((<) : α → α → Prop) ↪r ((<) : β → β → Prop) :=
{ map_rel_iff' := by intros; simp [lt_iff_le_not_le, f.map_rel_iff], .. f }

@[simp] lemma lt_embedding_apply (x : α) : f.lt_embedding x = f x := rfl

@[simp] theorem le_iff_le {a b} : (f a) ≤ (f b) ↔ a ≤ b := f.map_rel_iff

@[simp] theorem lt_iff_lt {a b} : f a < f b ↔ a < b :=
f.lt_embedding.map_rel_iff

@[simp] lemma eq_iff_eq {a b} : f a = f b ↔ a = b := f.injective.eq_iff

protected theorem monotone : monotone f := λ x y, f.le_iff_le.2

protected theorem strict_mono : strict_mono f := λ x y, f.lt_iff_lt.2

protected theorem acc (a : α) : acc (<) (f a) → acc (<) a :=
f.lt_embedding.acc a

protected theorem well_founded :
  well_founded ((<) : β → β → Prop) → well_founded ((<) : α → α → Prop) :=
f.lt_embedding.well_founded

protected theorem is_well_order [is_well_order β (<)] : is_well_order α (<) :=
f.lt_embedding.is_well_order

/-- An order embedding is also an order embedding between dual orders. -/
protected def dual : order_dual α ↪o order_dual β :=
⟨f.to_embedding, λ a b, f.map_rel_iff⟩

/--
To define an order embedding from a partial order to a preorder it suffices to give a function
together with a proof that it satisfies `f a ≤ f b ↔ a ≤ b`.
-/
def of_map_rel_iff {α β} [partial_order α] [preorder β] (f : α → β)
  (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) : α ↪o β :=
rel_embedding.of_map_rel_iff f hf

@[simp] lemma coe_of_map_rel_iff {α β} [partial_order α] [preorder β] {f : α → β} (h) :
  ⇑(of_map_rel_iff f h) = f := rfl

/-- A strictly monotone map from a linear order is an order embedding. --/
def of_strict_mono {α β} [linear_order α] [preorder β] (f : α → β)
  (h : strict_mono f) : α ↪o β :=
of_map_rel_iff f (λ _ _, h.le_iff_le)

@[simp] lemma coe_of_strict_mono {α β} [linear_order α] [preorder β] {f : α → β}
  (h : strict_mono f) : ⇑(of_strict_mono f h) = f := rfl

/-- Embedding of a subtype into the ambient type as an `order_embedding`. -/
@[simps {fully_applied := ff}] def subtype (p : α → Prop) : subtype p ↪o α :=
⟨embedding.subtype p, λ x y, iff.rfl⟩

end order_embedding

/-- A relation isomorphism is an equivalence that is also a relation embedding. -/
structure rel_iso {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ≃ β :=
(map_rel_iff' : ∀ {a b}, s (to_equiv a) (to_equiv b) ↔ r a b)

infix ` ≃r `:25 := rel_iso

/-- An order isomorphism is an equivalence such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `rel_iso (≤) (≤)`. -/
abbreviation order_iso (α β : Type*) [has_le α] [has_le β] := @rel_iso α β (≤) (≤)

infix ` ≃o `:25 := order_iso

namespace rel_iso

/-- Convert an `rel_iso` to an `rel_embedding`. This function is also available as a coercion
but often it is easier to write `f.to_rel_embedding` than to write explicitly `r` and `s`
in the target type. -/
def to_rel_embedding (f : r ≃r s) : r ↪r s :=
⟨f.to_equiv.to_embedding, f.map_rel_iff'⟩

instance : has_coe (r ≃r s) (r ↪r s) := ⟨to_rel_embedding⟩
-- see Note [function coercion]
instance : has_coe_to_fun (r ≃r s) := ⟨λ _, α → β, λ f, f⟩

@[simp] lemma to_rel_embedding_eq_coe (f : r ≃r s) : f.to_rel_embedding = f := rfl

@[simp] lemma coe_coe_fn (f : r ≃r s) : ((f : r ↪r s) : α → β) = f := rfl

theorem map_rel_iff (f : r ≃r s) : ∀ {a b}, s (f a) (f b) ↔ r a b := f.map_rel_iff'

@[simp] theorem coe_fn_mk (f : α ≃ β) (o : ∀ ⦃a b⦄, s (f a) (f b) ↔ r a b) :
  (rel_iso.mk f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_equiv (f : r ≃r s) : (f.to_equiv : α → β) = f := rfl

theorem to_equiv_injective : injective (to_equiv : (r ≃r s) → α ≃ β)
| ⟨e₁, o₁⟩ ⟨e₂, o₂⟩ h := by { congr, exact h }

/-- The map `coe_fn : (r ≃r s) → (α → β)` is injective. Lean fails to parse
`function.injective (λ e : r ≃r s, (e : α → β))`, so we use a trick to say the same. -/
theorem coe_fn_injective : function.injective (λ (e : r ≃r s) (x : α), e x) :=
equiv.coe_fn_injective.comp to_equiv_injective

@[ext] theorem ext ⦃f g : r ≃r s⦄ (h : ∀ x, f x = g x) : f = g :=
coe_fn_injective (funext h)

theorem ext_iff {f g : r ≃r s} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

/-- Inverse map of a relation isomorphism is a relation isomorphism. -/
@[symm] protected def symm (f : r ≃r s) : s ≃r r :=
⟨f.to_equiv.symm, λ a b, by erw [← f.map_rel_iff, f.1.apply_symm_apply, f.1.apply_symm_apply]⟩

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : r ≃r s) : α → β := h
/-- See Note [custom simps projection]. -/
def simps.symm_apply (h : r ≃r s) : β → α := h.symm

initialize_simps_projections rel_iso
  (to_equiv_to_fun → apply, to_equiv_inv_fun → symm_apply, -to_equiv)

/-- Identity map is a relation isomorphism. -/
@[refl, simps apply] protected def refl (r : α → α → Prop) : r ≃r r :=
⟨equiv.refl _, λ a b, iff.rfl⟩

/-- Composition of two relation isomorphisms is a relation isomorphism. -/
@[trans, simps apply] protected def trans (f₁ : r ≃r s) (f₂ : s ≃r t) : r ≃r t :=
⟨f₁.to_equiv.trans f₂.to_equiv, λ a b, f₂.map_rel_iff.trans f₁.map_rel_iff⟩

instance (r : α → α → Prop) : inhabited (r ≃r r) := ⟨rel_iso.refl _⟩

@[simp] lemma default_def (r : α → α → Prop) : default (r ≃r r) = rel_iso.refl r := rfl

/-- a relation isomorphism is also a relation isomorphism between dual relations. -/
protected def swap (f : r ≃r s) : (swap r) ≃r (swap s) :=
⟨f.to_equiv, λ _ _, f.map_rel_iff⟩

@[simp] theorem coe_fn_symm_mk (f o) : ((@rel_iso.mk _ _ r s f o).symm : β → α) = f.symm :=
rfl

@[simp] theorem apply_symm_apply  (e : r ≃r s) (x : β) : e (e.symm x) = x :=
e.to_equiv.apply_symm_apply x

@[simp] theorem symm_apply_apply (e : r ≃r s) (x : α) : e.symm (e x) = x :=
e.to_equiv.symm_apply_apply x

theorem rel_symm_apply (e : r ≃r s) {x y} : r x (e.symm y) ↔ s (e x) y :=
by rw [← e.map_rel_iff, e.apply_symm_apply]

theorem symm_apply_rel (e : r ≃r s) {x y} : r (e.symm x) y ↔ s x (e y) :=
by rw [← e.map_rel_iff, e.apply_symm_apply]

protected lemma bijective (e : r ≃r s) : bijective e := e.to_equiv.bijective
protected lemma injective (e : r ≃r s) : injective e := e.to_equiv.injective
protected lemma surjective (e : r ≃r s) : surjective e := e.to_equiv.surjective

@[simp] lemma range_eq (e : r ≃r s) : set.range e = set.univ := e.surjective.range_eq

@[simp] lemma eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b :=
f.injective.eq_iff

/-- Any equivalence lifts to a relation isomorphism between `s` and its preimage. -/
protected def preimage (f : α ≃ β) (s : β → β → Prop) : f ⁻¹'o s ≃r s := ⟨f, λ a b, iff.rfl⟩

/-- A surjective relation embedding is a relation isomorphism. -/
@[simps apply]
noncomputable def of_surjective (f : r ↪r s) (H : surjective f) : r ≃r s :=
⟨equiv.of_bijective f ⟨f.injective, H⟩, λ a b, f.map_rel_iff⟩

/--
Given relation isomorphisms `r₁ ≃r r₂` and `s₁ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the sum.
-/
def sum_lex_congr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂}
  (e₁ : @rel_iso α₁ α₂ r₁ r₂) (e₂ : @rel_iso β₁ β₂ s₁ s₂) :
  sum.lex r₁ s₁ ≃r sum.lex r₂ s₂ :=
⟨equiv.sum_congr e₁.to_equiv e₂.to_equiv, λ a b,
 by cases e₁ with f hf; cases e₂ with g hg;
    cases a; cases b; simp [hf, hg]⟩

/--
Given relation isomorphisms `r₁ ≃r r₂` and `s₁ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the product.
-/
def prod_lex_congr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂}
  (e₁ : @rel_iso α₁ α₂ r₁ r₂) (e₂ : @rel_iso β₁ β₂ s₁ s₂) :
  prod.lex r₁ s₁ ≃r prod.lex r₂ s₂ :=
⟨equiv.prod_congr e₁.to_equiv e₂.to_equiv,
  λ a b, by simp [prod.lex_def, e₁.map_rel_iff, e₂.map_rel_iff]⟩

instance : group (r ≃r r) :=
{ one := rel_iso.refl r,
  mul := λ f₁ f₂, f₂.trans f₁,
  inv := rel_iso.symm,
  mul_assoc := λ f₁ f₂ f₃, rfl,
  one_mul := λ f, ext $ λ _, rfl,
  mul_one := λ f, ext $ λ _, rfl,
  mul_left_inv := λ f, ext f.symm_apply_apply }

@[simp] lemma coe_one : ⇑(1 : r ≃r r) = id := rfl

@[simp] lemma coe_mul (e₁ e₂ : r ≃r r) : ⇑(e₁ * e₂) = e₁ ∘ e₂ := rfl

lemma mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp] lemma inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x := e.symm_apply_apply x

@[simp] lemma apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x := e.apply_symm_apply x

end rel_iso

namespace order_iso

section has_le

variables [has_le α] [has_le β] [has_le γ]

/-- Reinterpret an order isomorphism as an order embedding. -/
def to_order_embedding (e : α ≃o β) : α ↪o β :=
e.to_rel_embedding

@[simp] lemma coe_to_order_embedding (e : α ≃o β) :
  ⇑(e.to_order_embedding) = e := rfl

protected lemma bijective (e : α ≃o β) : bijective e := e.to_equiv.bijective
protected lemma injective (e : α ≃o β) : injective e := e.to_equiv.injective
protected lemma surjective (e : α ≃o β) : surjective e := e.to_equiv.surjective

@[simp] lemma range_eq (e : α ≃o β) : set.range e = set.univ := e.surjective.range_eq

@[simp] lemma apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x = e y ↔ x = y :=
e.to_equiv.apply_eq_iff_eq

/-- Identity order isomorphism. -/
def refl (α : Type*) [has_le α] : α ≃o α := rel_iso.refl (≤)

@[simp] lemma coe_refl : ⇑(refl α) = id := rfl

lemma refl_apply (x : α) : refl α x = x := rfl

@[simp] lemma refl_to_equiv : (refl α).to_equiv = equiv.refl α := rfl

/-- Inverse of an order isomorphism. -/
def symm (e : α ≃o β) : β ≃o α := e.symm

@[simp] lemma apply_symm_apply (e : α ≃o β) (x : β) : e (e.symm x) = x :=
e.to_equiv.apply_symm_apply x

@[simp] lemma symm_apply_apply (e : α ≃o β) (x : α) : e.symm (e x) = x :=
e.to_equiv.symm_apply_apply x

@[simp] lemma symm_refl (α : Type*) [has_le α] : (refl α).symm = refl α := rfl

lemma apply_eq_iff_eq_symm_apply (e : α ≃o β) (x : α) (y : β) : e x = y ↔ x = e.symm y :=
e.to_equiv.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.symm y = x ↔ y = e x :=
e.to_equiv.symm_apply_eq

@[simp] lemma symm_symm (e : α ≃o β) : e.symm.symm = e := by { ext, refl }

lemma symm_injective : injective (symm : (α ≃o β) → (β ≃o α)) :=
λ e e' h, by rw [← e.symm_symm, h, e'.symm_symm]

@[simp] lemma to_equiv_symm (e : α ≃o β) : e.to_equiv.symm = e.symm.to_equiv := rfl

/-- Composition of two order isomorphisms is an order isomorphism. -/
@[trans] def trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ := e.trans e'

@[simp] lemma coe_trans (e : α ≃o β) (e' : β ≃o γ) : ⇑(e.trans e') = e' ∘ e := rfl

lemma trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e.trans e' x = e' (e x) := rfl

@[simp] lemma refl_trans (e : α ≃o β) : (refl α).trans e = e := by { ext x, refl }

@[simp] lemma trans_refl (e : α ≃o β) : e.trans (refl β) = e := by { ext x, refl }

end has_le

open set

variables [preorder α] [preorder β] [preorder γ]

protected lemma monotone (e : α ≃o β) : monotone e := e.to_order_embedding.monotone

protected lemma strict_mono (e : α ≃o β) : strict_mono e := e.to_order_embedding.strict_mono

@[simp] lemma le_iff_le (e : α ≃o β) {x y : α} : e x ≤ e y ↔ x ≤ y := e.map_rel_iff

@[simp] lemma lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y :=
e.to_order_embedding.lt_iff_lt

@[simp] lemma preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' (Iic b) = Iic (e.symm b) :=
by { ext x, simp [← e.le_iff_le] }

@[simp] lemma preimage_Ici (e : α ≃o β) (b : β) : e ⁻¹' (Ici b) = Ici (e.symm b) :=
by { ext x, simp [← e.le_iff_le] }

@[simp] lemma preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' (Iio b) = Iio (e.symm b) :=
by { ext x, simp [← e.lt_iff_lt] }

@[simp] lemma preimage_Ioi (e : α ≃o β) (b : β) : e ⁻¹' (Ioi b) = Ioi (e.symm b) :=
by { ext x, simp [← e.lt_iff_lt] }

@[simp] lemma preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' (Icc a b) = Icc (e.symm a) (e.symm b) :=
by simp [← Ici_inter_Iic]

@[simp] lemma preimage_Ico (e : α ≃o β) (a b : β) : e ⁻¹' (Ico a b) = Ico (e.symm a) (e.symm b) :=
by simp [← Ici_inter_Iio]

@[simp] lemma preimage_Ioc (e : α ≃o β) (a b : β) : e ⁻¹' (Ioc a b) = Ioc (e.symm a) (e.symm b) :=
by simp [← Ioi_inter_Iic]

@[simp] lemma preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' (Ioo a b) = Ioo (e.symm a) (e.symm b) :=
by simp [← Ioi_inter_Iio]

/-- To show that `f : α → β`, `g : β → α` make up an order isomorphism of linear orders,
    it suffices to prove `cmp a (g b) = cmp (f a) b`. --/
def of_cmp_eq_cmp {α β} [linear_order α] [linear_order β] (f : α → β) (g : β → α)
  (h : ∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β :=
have gf : ∀ (a : α), a = g (f a) := by { intro, rw [←cmp_eq_eq_iff, h, cmp_self_eq_eq] },
{ to_fun := f,
  inv_fun := g,
  left_inv := λ a, (gf a).symm,
  right_inv := by { intro, rw [←cmp_eq_eq_iff, ←h, cmp_self_eq_eq] },
  map_rel_iff' := by { intros, apply le_iff_le_of_cmp_eq_cmp, convert (h _ _).symm, apply gf } }

/-- Order isomorphism between two equal sets. -/
def set_congr (s t : set α) (h : s = t) : s ≃o t :=
{ to_equiv := equiv.set_congr h,
  map_rel_iff' := λ x y, iff.rfl }

/-- Order isomorphism between `univ : set α` and `α`. -/
def set.univ : (set.univ : set α) ≃o α :=
{ to_equiv := equiv.set.univ α,
  map_rel_iff' := λ x y, iff.rfl }

end order_iso

/-- If a function `f` is strictly monotone on a set `s`, then it defines an order isomorphism
between `s` and its image. -/
protected noncomputable def strict_mono_incr_on.order_iso {α β} [linear_order α] [preorder β]
  (f : α → β) (s : set α) (hf : strict_mono_incr_on f s) :
  s ≃o f '' s :=
{ to_equiv := hf.inj_on.bij_on_image.equiv _,
  map_rel_iff' := λ x y, hf.le_iff_le x.2 y.2 }

/-- A strictly monotone function from a linear order is an order isomorphism between its domain and
its range. -/
protected noncomputable def strict_mono.order_iso {α β} [linear_order α] [preorder β] (f : α → β)
  (h_mono : strict_mono f) : α ≃o set.range f :=
{ to_equiv := equiv.of_injective f h_mono.injective,
  map_rel_iff' := λ a b, h_mono.le_iff_le }

/-- A strictly monotone surjective function from a linear order is an order isomorphism. -/
noncomputable def strict_mono.order_iso_of_surjective {α β} [linear_order α] [preorder β]
  (f : α → β) (h_mono : strict_mono f) (h_surj : surjective f) : α ≃o β :=
(h_mono.order_iso f).trans $ (order_iso.set_congr _ _ h_surj.range_eq).trans order_iso.set.univ

/-- `subrel r p` is the inherited relation on a subset. -/
def subrel (r : α → α → Prop) (p : set α) : p → p → Prop :=
(coe : p → α) ⁻¹'o r

@[simp] theorem subrel_val (r : α → α → Prop) (p : set α)
  {a b} : subrel r p a b ↔ r a.1 b.1 := iff.rfl

namespace subrel

/-- The relation embedding from the inherited relation on a subset. -/
protected def rel_embedding (r : α → α → Prop) (p : set α) :
  subrel r p ↪r r := ⟨embedding.subtype _, λ a b, iff.rfl⟩

@[simp] theorem rel_embedding_apply (r : α → α → Prop) (p a) :
  subrel.rel_embedding r p a = a.1 := rfl

instance (r : α → α → Prop) [is_well_order α r]
  (p : set α) : is_well_order p (subrel r p) :=
rel_embedding.is_well_order (subrel.rel_embedding r p)

end subrel

/-- Restrict the codomain of a relation embedding. -/
def rel_embedding.cod_restrict (p : set β) (f : r ↪r s) (H : ∀ a, f a ∈ p) : r ↪r subrel s p :=
⟨f.to_embedding.cod_restrict p H, f.map_rel_iff'⟩

@[simp] theorem rel_embedding.cod_restrict_apply (p) (f : r ↪r s) (H a) :
  rel_embedding.cod_restrict p f H a = ⟨f a, H a⟩ := rfl

  /-- An order isomorphism is also an order isomorphism between dual orders. -/
protected def order_iso.dual [preorder α] [preorder β] (f : α ≃o β) :
  order_dual α ≃o order_dual β := ⟨f.to_equiv, λ _ _, f.map_rel_iff⟩

section lattice_isos

lemma order_iso.map_bot' [partial_order α] [partial_order β] (f : α ≃o β) {x : α} {y : β}
  (hx : ∀ x', x ≤ x') (hy : ∀ y', y ≤ y') : f x = y :=
by { refine le_antisymm _ (hy _), rw [← f.apply_symm_apply y, f.map_rel_iff], apply hx }

lemma order_iso.map_bot [order_bot α] [order_bot β] (f : α ≃o β) : f ⊥ = ⊥ :=
f.map_bot' (λ _, bot_le) (λ _, bot_le)

lemma order_iso.map_top' [partial_order α] [partial_order β] (f : α ≃o β) {x : α} {y : β}
  (hx : ∀ x', x' ≤ x) (hy : ∀ y', y' ≤ y) : f x = y :=
f.dual.map_bot' hx hy

lemma order_iso.map_top [order_top α] [order_top β] (f : α ≃o β) : f ⊤ = ⊤ :=
f.dual.map_bot

lemma order_embedding.map_inf_le [semilattice_inf α] [semilattice_inf β]
  (f : α ↪o β) (x y : α) :
  f (x ⊓ y) ≤ f x ⊓ f y :=
f.monotone.map_inf_le x y

lemma order_iso.map_inf [semilattice_inf α] [semilattice_inf β]
  (f : α ≃o β) (x y : α) :
  f (x ⊓ y) = f x ⊓ f y :=
begin
  refine (f.to_order_embedding.map_inf_le x y).antisymm _,
  simpa [← f.symm.le_iff_le] using f.symm.to_order_embedding.map_inf_le (f x) (f y)
end

lemma order_embedding.le_map_sup [semilattice_sup α] [semilattice_sup β]
  (f : α ↪o β) (x y : α) :
  f x ⊔ f y ≤ f (x ⊔ y) :=
f.monotone.le_map_sup x y

lemma order_iso.map_sup [semilattice_sup α] [semilattice_sup β]
  (f : α ≃o β) (x y : α) :
  f (x ⊔ y) = f x ⊔ f y :=
f.dual.map_inf x y

/-- Order isomorphism between `Iic (⊤ : α)` and `α` when `α` has a top element -/
def order_iso.Iic_top [order_top α] : set.Iic (⊤ : α) ≃o α :=
{ map_rel_iff' := λ x y, by refl,
  .. (@equiv.subtype_univ_equiv α (set.Iic (⊤ : α)) (λ x, le_top)), }

/-- Order isomorphism between `Ici (⊥ : α)` and `α` when `α` has a bottom element -/
def order_iso.Ici_bot [order_bot α] : set.Ici (⊥ : α) ≃o α :=
{ map_rel_iff' := λ x y, by refl,
  .. (@equiv.subtype_univ_equiv α (set.Ici (⊥ : α)) (λ x, bot_le)) }

section bounded_lattice

variables [bounded_lattice α]  [bounded_lattice β] (f : α ≃o β)
include f

lemma order_iso.is_compl {x y : α} (h : is_compl x y) : is_compl (f x) (f y) :=
⟨by { rw [← f.map_bot, ← f.map_inf, f.map_rel_iff], exact h.1 },
  by { rw [← f.map_top, ← f.map_sup, f.map_rel_iff], exact h.2 }⟩

theorem order_iso.is_compl_iff {x y : α} :
  is_compl x y ↔ is_compl (f x) (f y) :=
⟨f.is_compl, λ h, begin
  rw [← f.symm_apply_apply x, ← f.symm_apply_apply y],
  exact f.symm.is_compl h,
end⟩

lemma order_iso.is_complemented
  [is_complemented α] : is_complemented β :=
⟨λ x, begin
  obtain ⟨y, hy⟩ := exists_is_compl (f.symm x),
  rw ← f.symm_apply_apply y at hy,
  refine ⟨f y, f.symm.is_compl_iff.2 hy⟩,
end⟩

theorem order_iso.is_complemented_iff :
  is_complemented α ↔ is_complemented β :=
⟨by { introI, exact f.is_complemented }, by { introI, exact f.symm.is_complemented }⟩

end bounded_lattice
end lattice_isos
