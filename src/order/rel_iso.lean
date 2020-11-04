/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import logic.embedding
import order.rel_classes
import data.fin

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
@[refl] protected def id (r : α → α → Prop) : r →r r :=
⟨id, λ a b, id⟩

/-- Composition of two relation homomorphisms is a relation homomorphism. -/
@[trans] protected def comp (g : s →r t) (f : r →r s) : r →r t :=
⟨g.1 ∘ f.1, λ a b h, g.2 (f.2 h)⟩

@[simp] theorem id_apply (x : α) : rel_hom.id r x = x := rfl

@[simp] theorem comp_apply (g : s →r t) (f : r →r s) (a : α) : (g.comp f) a = g (f a) := rfl

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
(map_rel_iff' : ∀ {a b}, r a b ↔ s (to_embedding a) (to_embedding b))

infix ` ↪r `:25 := rel_embedding

/-- An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `rel_embedding (≤) (≤)`. -/
abbreviation order_embedding (α β : Type*) [has_le α] [has_le β] :=
@rel_embedding α β (≤) (≤)

infix ` ↪o `:25 := order_embedding

/-- The induced relation on a subtype is an embedding under the natural inclusion. -/
definition subtype.rel_embedding {X : Type*} (r : X → X → Prop) (p : X → Prop) :
((subtype.val : subtype p → X) ⁻¹'o r) ↪r r :=
⟨⟨subtype.val,subtype.val_injective⟩,by intros;refl⟩

theorem preimage_equivalence {α β} (f : α → β) {s : β → β → Prop}
  (hs : equivalence s) : equivalence (f ⁻¹'o s) :=
⟨λ a, hs.1 _, λ a b h, hs.2.1 h, λ a b c h₁ h₂, hs.2.2 h₁ h₂⟩

namespace rel_embedding

/-- A relation embedding is also a relation homomorphism -/
def to_rel_hom (f : r ↪r s) : (r →r s) :=
{ to_fun := f.to_embedding.to_fun,
  map_rel' := λ x y, (map_rel_iff' f).mp }

instance : has_coe (r ↪r s) (r →r s) := ⟨to_rel_hom⟩
-- see Note [function coercion]
instance : has_coe_to_fun (r ↪r s) := ⟨λ _, α → β, λ o, o.to_embedding⟩

@[simp] lemma to_rel_hom_eq_coe (f : r ↪r s) : f.to_rel_hom = f := rfl

@[simp] lemma coe_coe_fn (f : r ↪r s) : ((f : r →r s) : α → β) = f := rfl

theorem injective (f : r ↪r s) : injective f := f.inj'

theorem map_rel_iff (f : r ↪r s) : ∀ {a b}, r a b ↔ s (f a) (f b) := f.map_rel_iff'

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
@[refl] protected def refl (r : α → α → Prop) : r ↪r r :=
⟨embedding.refl _, λ a b, iff.rfl⟩

/-- Composition of two relation embeddings is a relation embedding. -/
@[trans] protected def trans (f : r ↪r s) (g : s ↪r t) : r ↪r t :=
⟨f.1.trans g.1, λ a b, by rw [f.2, g.2]; simp⟩

instance (r : α → α → Prop) : inhabited (r ↪r r) := ⟨rel_embedding.refl _⟩

@[simp] theorem refl_apply (x : α) : rel_embedding.refl r x = x := rfl

@[simp] theorem trans_apply (f : r ↪r s) (g : s ↪r t) (a : α) : (f.trans g) a = g (f a) := rfl

/-- A relation embedding is also a relation embedding between dual relations. -/
protected def swap (f : r ↪r s) : swap r ↪r swap s :=
⟨f.to_embedding, λ a b, f.map_rel_iff⟩

/-- If `f` is injective, then it is a relation embedding from the
  preimage relation of `s` to `s`. -/
def preimage (f : α ↪ β) (s : β → β → Prop) : f ⁻¹'o s ↪r s := ⟨f, λ a b, iff.rfl⟩

theorem eq_preimage (f : r ↪r s) : r = f ⁻¹'o s :=
by { ext a b, exact f.map_rel_iff }

protected theorem is_irrefl : ∀ (f : r ↪r s) [is_irrefl β s], is_irrefl α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a h, H _ (o.1 h)⟩

protected theorem is_refl : ∀ (f : r ↪r s) [is_refl β s], is_refl α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a, o.2 (H _)⟩

protected theorem is_symm : ∀ (f : r ↪r s) [is_symm β s], is_symm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h, o.2 (H _ _ (o.1 h))⟩

protected theorem is_asymm : ∀ (f : r ↪r s) [is_asymm β s], is_asymm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h₁ h₂, H _ _ (o.1 h₁) (o.1 h₂)⟩

protected theorem is_antisymm : ∀ (f : r ↪r s) [is_antisymm β s], is_antisymm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h₁ h₂, f.inj' (H _ _ (o.1 h₁) (o.1 h₂))⟩

protected theorem is_trans : ∀ (f : r ↪r s) [is_trans β s], is_trans α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b c h₁ h₂, o.2 (H _ _ _ (o.1 h₁) (o.1 h₂))⟩

protected theorem is_total : ∀ (f : r ↪r s) [is_total β s], is_total α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o o).2 (H _ _)⟩

protected theorem is_preorder : ∀ (f : r ↪r s) [is_preorder β s], is_preorder α r
| f H := by exactI {..f.is_refl, ..f.is_trans}

protected theorem is_partial_order : ∀ (f : r ↪r s) [is_partial_order β s], is_partial_order α r
| f H := by exactI {..f.is_preorder, ..f.is_antisymm}

protected theorem is_linear_order : ∀ (f : r ↪r s) [is_linear_order β s], is_linear_order α r
| f H := by exactI {..f.is_partial_order, ..f.is_total}

protected theorem is_strict_order : ∀ (f : r ↪r s) [is_strict_order β s], is_strict_order α r
| f H := by exactI {..f.is_irrefl, ..f.is_trans}

protected theorem is_trichotomous : ∀ (f : r ↪r s) [is_trichotomous β s], is_trichotomous α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o (or_congr f.inj'.eq_iff.symm o)).2 (H _ _)⟩

protected theorem is_strict_total_order' :
  ∀ (f : r ↪r s) [is_strict_total_order' β s], is_strict_total_order' α r
| f H := by exactI {..f.is_trichotomous, ..f.is_strict_order}

protected theorem acc (f : r ↪r s) (a : α) : acc s (f a) → acc r a :=
begin
  generalize h : f a = b, intro ac,
  induction ac with _ H IH generalizing a, subst h,
  exact ⟨_, λ a' h, IH (f a') (f.map_rel_iff.1 h) _ rfl⟩
end

protected theorem well_founded : ∀ (f : r ↪r s) (h : well_founded s), well_founded r
| f ⟨H⟩ := ⟨λ a, f.acc _ (H _)⟩

protected theorem is_well_order : ∀ (f : r ↪r s) [is_well_order β s], is_well_order α r
| f H := by exactI {wf := f.well_founded H.wf, ..f.is_strict_total_order'}

/-- It suffices to prove `f` is monotone between strict relations
  to show it is a relation embedding. -/
def of_monotone [is_trichotomous α r] [is_asymm β s] (f : α → β)
  (H : ∀ a b, r a b → s (f a) (f b)) : r ↪r s :=
begin
  haveI := @is_asymm.is_irrefl β s _,
  refine ⟨⟨f, λ a b e, _⟩, λ a b, ⟨H _ _, λ h, _⟩⟩,
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
{ map_rel_iff' := by { intros, simp [le_iff_lt_or_eq,f.map_rel_iff, f.injective] }, .. f }

end rel_embedding

namespace order_embedding

variables [preorder α] [preorder β] (f : α ↪o β)

/-- lt is preserved by order embeddings of preorders -/
def lt_embedding : ((<) : α → α → Prop) ↪r ((<) : β → β → Prop) :=
{ map_rel_iff' := by intros; simp [lt_iff_le_not_le,f.map_rel_iff], .. f }

@[simp] lemma lt_embedding_apply (x : α) : f.lt_embedding x = f x := rfl

theorem map_le_iff : ∀ {a b}, a ≤ b ↔ (f a) ≤ (f b) := f.map_rel_iff'

theorem map_lt_iff : ∀ {a b}, a < b ↔ (f a) < (f b) :=
f.lt_embedding.map_rel_iff'

protected theorem monotone : monotone f := λ x y, f.map_le_iff.1

protected theorem strict_mono : strict_mono f := λ x y, f.map_lt_iff.1

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

/-- A sctrictly monotone map from a linear order is an order embedding. --/
def of_strict_mono {α β} [linear_order α] [preorder β] (f : α → β)
  (h : strict_mono f) : α ↪o β :=
{ to_fun := f,
  inj' := strict_mono.injective h,
  map_rel_iff' := begin
    intros,
    rcases lt_trichotomy a b with lt | eq | gt,
    { exact iff_of_true (le_of_lt lt) (le_of_lt (h lt)) },
    { rw eq, apply iff_of_true, refl, refl },
    { apply iff_of_false (not_le_of_gt gt) (not_le_of_gt (h gt)) }
  end }

end order_embedding

/-- The inclusion map `fin n → ℕ` is a relation embedding. -/
def fin.val.rel_embedding (n) : (fin n) ↪o ℕ :=
⟨⟨coe, @fin.eq_of_veq _⟩, λ a b, iff.rfl⟩

/-- The inclusion map `fin m → fin n` is an order embedding. -/
def fin_fin.rel_embedding {m n} (h : m ≤ n) : (fin m) ↪o (fin n) :=
⟨⟨λ ⟨x, h'⟩, ⟨x, lt_of_lt_of_le h' h⟩,
  λ ⟨a, _⟩ ⟨b, _⟩ h, by congr; injection h⟩,
  by intros; cases a; cases b; refl⟩

/-- The ordering on `fin n` is a well order. -/
instance fin.lt.is_well_order (n) : is_well_order (fin n) (<) :=
(fin.val.rel_embedding n).is_well_order

/-- A relation isomorphism is an equivalence that is also a relation embedding. -/
structure rel_iso {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ≃ β :=
(map_rel_iff' : ∀ {a b}, r a b ↔ s (to_equiv a) (to_equiv b))

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

theorem map_rel_iff (f : r ≃r s) : ∀ {a b}, r a b ↔ s (f a) (f b) := f.map_rel_iff'

lemma map_rel_iff'' {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) {x y : α} :
    r x y ↔ s ((↑f : r ↪r s) x) ((↑f : r ↪r s) y) := f.map_rel_iff

@[simp] theorem coe_fn_mk (f : α ≃ β) (o : ∀ ⦃a b⦄, r a b ↔ s (f a) (f b)) :
  (rel_iso.mk f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_equiv (f : r ≃r s) : (f.to_equiv : α → β) = f := rfl

theorem injective_to_equiv : injective (to_equiv : (r ≃r s) → α ≃ β)
| ⟨e₁, o₁⟩ ⟨e₂, o₂⟩ h := by { congr, exact h }

/-- The map `coe_fn : (r ≃r s) → (α → β)` is injective. Lean fails to parse
`function.injective (λ e : r ≃r s, (e : α → β))`, so we use a trick to say the same. -/
theorem injective_coe_fn : function.injective (λ (e : r ≃r s) (x : α), e x) :=
equiv.injective_coe_fn.comp injective_to_equiv

@[ext] theorem ext ⦃f g : r ≃r s⦄ (h : ∀ x, f x = g x) : f = g :=
injective_coe_fn (funext h)

theorem ext_iff {f g : r ≃r s} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

/-- Identity map is a relation isomorphism. -/
@[refl] protected def refl (r : α → α → Prop) : r ≃r r :=
⟨equiv.refl _, λ a b, iff.rfl⟩

/-- Inverse map of a relation isomorphism is a relation isomorphism. -/
@[symm] protected def symm (f : r ≃r s) : s ≃r r :=
⟨f.to_equiv.symm, λ a b, by cases f with f o; rw o; simp⟩

/-- Composition of two relation isomorphisms is a relation isomorphism. -/
@[trans] protected def trans (f₁ : r ≃r s) (f₂ : s ≃r t) : r ≃r t :=
⟨f₁.to_equiv.trans f₂.to_equiv, λ a b, f₁.map_rel_iff.trans f₂.map_rel_iff⟩

instance (r : α → α → Prop) : inhabited (r ≃r r) := ⟨rel_iso.refl _⟩

/-- a relation isomorphism is also a relation isomorphism between dual relations. -/
protected def swap (f : r ≃r s) : (swap r) ≃r (swap s) :=
⟨f.to_equiv, λ _ _, f.map_rel_iff⟩

@[simp] theorem coe_fn_symm_mk (f o) : ((@rel_iso.mk _ _ r s f o).symm : β → α) = f.symm :=
rfl

@[simp] theorem refl_apply (x : α) : rel_iso.refl r x = x := rfl

@[simp] theorem trans_apply (f : r ≃r s) (g : s ≃r t) (a : α) : (f.trans g) a = g (f a) :=
rfl

@[simp] theorem apply_symm_apply  (e : r ≃r s) (x : β) : e (e.symm x) = x :=
e.to_equiv.apply_symm_apply x

@[simp] theorem symm_apply_apply (e : r ≃r s) (x : α) : e.symm (e x) = x :=
e.to_equiv.symm_apply_apply x

theorem rel_symm_apply (e : r ≃r s) {x y} : r x (e.symm y) ↔ s (e x) y :=
by rw [e.map_rel_iff, e.apply_symm_apply]

theorem symm_apply_rel (e : r ≃r s) {x y} : r (e.symm x) y ↔ s x (e y) :=
by rw [e.map_rel_iff, e.apply_symm_apply]

protected lemma bijective (e : r ≃r s) : bijective e := e.to_equiv.bijective
protected lemma injective (e : r ≃r s) : injective e := e.to_equiv.injective
protected lemma surjective (e : r ≃r s) : surjective e := e.to_equiv.surjective

/-- Any equivalence lifts to a relation isomorphism between `s` and its preimage. -/
protected def preimage (f : α ≃ β) (s : β → β → Prop) : f ⁻¹'o s ≃r s := ⟨f, λ a b, iff.rfl⟩

/-- A surjective relation embedding is a relation isomorphism. -/
noncomputable def of_surjective (f : r ↪r s) (H : surjective f) : r ≃r s :=
⟨equiv.of_bijective f ⟨f.injective, H⟩, by simp [f.map_rel_iff']⟩

@[simp] theorem of_surjective_coe (f : r ↪r s) (H) : (of_surjective f H : α → β) = f :=
rfl

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
⟨equiv.prod_congr e₁.to_equiv e₂.to_equiv,  λ a b, begin
  cases e₁ with f hf; cases e₂ with g hg,
  cases a with a₁ a₂; cases b with b₁ b₂,
  suffices : prod.lex r₁ s₁ (a₁, a₂) (b₁, b₂) ↔
    prod.lex r₂ s₂ (f a₁, g a₂) (f b₁, g b₂), {simpa [hf, hg]},
  split,
  { intro h, cases h with _ _ _ _ h _ _ _ h,
    { left, exact hf.1 h },
    { right, exact hg.1 h } },
  { generalize e : f b₁ = fb₁,
    intro h, cases h with _ _ _ _ h _ _ _ h,
    { subst e, left, exact hf.2 h },
    { have := f.injective e, subst b₁,
      right, exact hg.2 h } }
end⟩

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

/-- Reinterpret an order isomorphism as an order embedding. -/
def to_order_embedding [has_le α] [has_le β] (e : α ≃o β) : α ↪o β :=
e.to_rel_embedding

@[simp] lemma coe_to_order_embedding [has_le α] [has_le β] (e : α ≃o β) :
  ⇑(e.to_order_embedding) = e := rfl

variables [preorder α] [preorder β]

protected lemma monotone (e : α ≃o β) : monotone e := e.to_order_embedding.monotone

protected lemma strict_mono (e : α ≃o β) : strict_mono e := e.to_order_embedding.strict_mono

/-- To show that `f : α → β`, `g : β → α` make up an order isomorphism of linear orders,
    it suffices to prove `cmp a (g b) = cmp (f a) b`. --/
def of_cmp_eq_cmp {α β} [linear_order α] [linear_order β] (f : α → β) (g : β → α)
  (h : ∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β :=
have gf : ∀ (a : α), a = g (f a) := by { intro, rw [←cmp_eq_eq_iff, h, cmp_self_eq_eq] },
{ to_fun := f,
  inv_fun := g,
  left_inv := λ a, (gf a).symm,
  right_inv := by { intro, rw [←cmp_eq_eq_iff, ←h, cmp_self_eq_eq] },
  map_rel_iff' := by { intros, apply le_iff_le_of_cmp_eq_cmp, convert h _ _, apply gf } }

end order_iso

/-- A subset `p : set α` embeds into `α` -/
def set_coe_embedding {α : Type*} (p : set α) : p ↪ α := ⟨subtype.val, @subtype.eq _ _⟩

/-- `subrel r p` is the inherited relation on a subset. -/
def subrel (r : α → α → Prop) (p : set α) : p → p → Prop :=
@subtype.val _ p ⁻¹'o r

@[simp] theorem subrel_val (r : α → α → Prop) (p : set α)
  {a b} : subrel r p a b ↔ r a.1 b.1 := iff.rfl

namespace subrel

/-- The relation embedding from the inherited relation on a subset. -/
protected def rel_embedding (r : α → α → Prop) (p : set α) :
  subrel r p ↪r r := ⟨set_coe_embedding _, λ a b, iff.rfl⟩

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

lemma order_iso.map_bot [order_bot α] [order_bot β]
  (f : α ≃o β) :
  f ⊥ = ⊥ :=
by { rw [eq_bot_iff, ← f.apply_symm_apply ⊥, ← f.map_rel_iff], apply bot_le, }

lemma rel_iso.map_top [order_top α] [order_top β]
  (f : α ≃o β) :
  f ⊤ = ⊤ :=
by { rw [eq_top_iff, ← f.apply_symm_apply ⊤, ← f.map_rel_iff], apply le_top, }

variables {a₁ a₂ : α}

lemma rel_embedding.map_inf_le [semilattice_inf α] [semilattice_inf β]
  (f : α ↪o β) :
  f (a₁ ⊓ a₂) ≤ f a₁ ⊓ f a₂ :=
by simp [← f.map_rel_iff]

lemma rel_iso.map_inf [semilattice_inf α] [semilattice_inf β]
  (f : α ≃o β) :
  f (a₁ ⊓ a₂) = f a₁ ⊓ f a₂ :=
begin
  apply le_antisymm, { apply f.to_rel_embedding.map_inf_le },
  rw [f.symm.map_rel_iff, rel_iso.symm_apply_apply],
  convert f.symm.to_rel_embedding.map_inf_le; simp,
end

lemma rel_embedding.le_map_sup [semilattice_sup α] [semilattice_sup β]
  (f : α ↪o β) :
  f a₁ ⊔ f a₂ ≤ f (a₁ ⊔ a₂) :=
by simp [← f.map_rel_iff]


lemma rel_iso.map_sup [semilattice_sup α] [semilattice_sup β]
  (f : α ≃o β) :
  f (a₁ ⊔ a₂) = f a₁ ⊔ f a₂ :=
begin
  apply le_antisymm, swap, { apply f.to_rel_embedding.le_map_sup },
  rw [f.symm.map_rel_iff, rel_iso.symm_apply_apply],
  convert f.symm.to_rel_embedding.le_map_sup; simp; simp
end

end lattice_isos
