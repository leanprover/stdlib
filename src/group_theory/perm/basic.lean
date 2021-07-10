/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import algebra.group.pi
import algebra.group_power

/-!
# The group of permutations (self-equivalences) of a type `α`

This file defines the `group` structure on `equiv.perm α`.
-/
universes u v

namespace equiv

variables {α : Type u} {β : Type v}

namespace perm

instance perm_group : group (perm α) :=
{ mul := λ f g, equiv.trans g f,
  one := equiv.refl α,
  inv := equiv.symm,
  mul_assoc := λ f g h, (trans_assoc _ _ _).symm,
  one_mul := trans_refl,
  mul_one := refl_trans,
  mul_left_inv := trans_symm }

theorem mul_apply (f g : perm α) (x) : (f * g) x = f (g x) :=
equiv.trans_apply _ _ _

theorem one_apply (x) : (1 : perm α) x = x := rfl

@[simp] lemma inv_apply_self (f : perm α) (x) : f⁻¹ (f x) = x := f.symm_apply_apply x

@[simp] lemma apply_inv_self (f : perm α) (x) : f (f⁻¹ x) = x := f.apply_symm_apply x

lemma one_def : (1 : perm α) = equiv.refl α := rfl

lemma mul_def (f g : perm α) : f * g = g.trans f := rfl

lemma inv_def (f : perm α) : f⁻¹ = f.symm := rfl

@[simp] lemma coe_mul (f g : perm α) : ⇑(f * g) = f ∘ g := rfl

@[simp] lemma coe_one : ⇑(1 : perm α) = id := rfl

lemma eq_inv_iff_eq {f : perm α} {x y : α} : x = f⁻¹ y ↔ f x = y := f.eq_symm_apply

lemma inv_eq_iff_eq {f : perm α} {x y : α} : f⁻¹ x = y ↔ x = f y := f.symm_apply_eq

lemma gpow_apply_comm {α : Type*} (σ : equiv.perm α) (m n : ℤ) {x : α} :
  (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) :=
by rw [←equiv.perm.mul_apply, ←equiv.perm.mul_apply, gpow_mul_comm]

/-! Lemmas about mixing `perm` with `equiv`. Because we have multiple ways to express
`equiv.refl`, `equiv.symm`, and `equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it after
simp. -/

@[simp] lemma trans_one {α : Sort*} {β : Type*} (e : α ≃ β) : e.trans (1 : perm β) = e :=
equiv.trans_refl e

@[simp] lemma mul_refl (e : perm α) : e * equiv.refl α = e := equiv.trans_refl e

@[simp] lemma one_symm : (1 : perm α).symm = 1 := equiv.refl_symm

@[simp] lemma refl_inv : (equiv.refl α : perm α)⁻¹ = 1 := equiv.refl_symm

@[simp] lemma one_trans {α : Type*} {β : Sort*} (e : α ≃ β) : (1 : perm α).trans e = e :=
equiv.refl_trans e

@[simp] lemma refl_mul (e : perm α) : equiv.refl α * e = e := equiv.refl_trans e

@[simp] lemma inv_trans (e : perm α) : e⁻¹.trans e = 1 := equiv.symm_trans e

@[simp] lemma mul_symm (e : perm α) : e * e.symm = 1 := equiv.symm_trans e

@[simp] lemma trans_inv (e : perm α) : e.trans e⁻¹ = 1 := equiv.trans_symm e

@[simp] lemma symm_mul (e : perm α) : e.symm * e = 1 := equiv.trans_symm e

/-! Lemmas about `equiv.perm.sum_congr` re-expressed via the group structure. -/

@[simp] lemma sum_congr_mul {α β : Type*} (e : perm α) (f : perm β) (g : perm α) (h : perm β) :
  sum_congr e f * sum_congr g h = sum_congr (e * g) (f * h) :=
sum_congr_trans g h e f

@[simp] lemma sum_congr_inv {α β : Type*} (e : perm α) (f : perm β) :
  (sum_congr e f)⁻¹ = sum_congr e⁻¹ f⁻¹ :=
sum_congr_symm e f

@[simp] lemma sum_congr_one {α β : Type*} :
  sum_congr (1 : perm α) (1 : perm β) = 1 :=
sum_congr_refl

/-- `equiv.perm.sum_congr` as a `monoid_hom`, with its two arguments bundled into a single `prod`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between `α` and `β`. -/
@[simps]
def sum_congr_hom (α β : Type*) :
  perm α × perm β →* perm (α ⊕ β) :=
{ to_fun := λ a, sum_congr a.1 a.2,
  map_one' := sum_congr_one,
  map_mul' := λ a b, (sum_congr_mul _ _ _ _).symm}

lemma sum_congr_hom_injective {α β : Type*} :
  function.injective (sum_congr_hom α β) :=
begin
  rintros ⟨⟩ ⟨⟩ h,
  rw prod.mk.inj_iff,
  split; ext i,
  { simpa using equiv.congr_fun h (sum.inl i), },
  { simpa using equiv.congr_fun h (sum.inr i), },
end

@[simp] lemma sum_congr_swap_one {α β : Type*} [decidable_eq α] [decidable_eq β] (i j : α) :
  sum_congr (equiv.swap i j) (1 : perm β) = equiv.swap (sum.inl i) (sum.inl j) :=
sum_congr_swap_refl i j

@[simp] lemma sum_congr_one_swap {α β : Type*} [decidable_eq α] [decidable_eq β] (i j : β) :
  sum_congr (1 : perm α) (equiv.swap i j) = equiv.swap (sum.inr i) (sum.inr j) :=
sum_congr_refl_swap i j

/-! Lemmas about `equiv.perm.sigma_congr_right` re-expressed via the group structure. -/

@[simp] lemma sigma_congr_right_mul {α : Type*} {β : α → Type*}
  (F : Π a, perm (β a)) (G : Π a, perm (β a)) :
  sigma_congr_right F * sigma_congr_right G = sigma_congr_right (F * G) :=
sigma_congr_right_trans G F

@[simp] lemma sigma_congr_right_inv {α : Type*} {β : α → Type*} (F : Π a, perm (β a)) :
  (sigma_congr_right F)⁻¹ = sigma_congr_right (λ a, (F a)⁻¹) :=
sigma_congr_right_symm F

@[simp] lemma sigma_congr_right_one {α : Type*} {β : α → Type*} :
  (sigma_congr_right (1 : Π a, equiv.perm $ β a)) = 1 :=
sigma_congr_right_refl

/-- `equiv.perm.sigma_congr_right` as a `monoid_hom`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between fibers. -/
@[simps]
def sigma_congr_right_hom {α : Type*} (β : α → Type*) :
  (Π a, perm (β a)) →* perm (Σ a, β a) :=
{ to_fun := sigma_congr_right,
  map_one' := sigma_congr_right_one,
  map_mul' := λ a b, (sigma_congr_right_mul _ _).symm }

lemma sigma_congr_right_hom_injective {α : Type*} {β : α → Type*} :
  function.injective (sigma_congr_right_hom β) :=
begin
  intros x y h,
  ext a b,
  simpa using equiv.congr_fun h ⟨a, b⟩,
end

/-- `equiv.perm.subtype_congr` as a `monoid_hom`. -/
@[simps] def subtype_congr_hom (p : α → Prop) [decidable_pred p] :
  (perm {a // p a}) × (perm {a // ¬ p a}) →* perm α :=
{ to_fun := λ pair, perm.subtype_congr pair.fst pair.snd,
  map_one' := perm.subtype_congr.refl,
  map_mul' := λ _ _, (perm.subtype_congr.trans _ _ _ _).symm }

lemma subtype_congr_hom_injective (p : α → Prop) [decidable_pred p] :
  function.injective (subtype_congr_hom p) :=
begin
  rintros ⟨⟩ ⟨⟩ h,
  rw prod.mk.inj_iff,
  split;
  ext i;
  simpa using equiv.congr_fun h i
end

/-- If `e` is also a permutation, we can write `perm_congr`
completely in terms of the group structure. -/
@[simp] lemma perm_congr_eq_mul (e p : perm α) :
  e.perm_congr p = e * p * e⁻¹ := rfl

section extend_domain

/-! Lemmas about `equiv.perm.extend_domain` re-expressed via the group structure. -/

variables (e : perm α) {p : β → Prop} [decidable_pred p] (f : α ≃ subtype p)

@[simp] lemma extend_domain_one : extend_domain 1 f = 1 :=
extend_domain_refl f

@[simp] lemma extend_domain_inv : (e.extend_domain f)⁻¹ = e⁻¹.extend_domain f := rfl

@[simp] lemma extend_domain_mul (e e' : perm α) :
  (e.extend_domain f) * (e'.extend_domain f) = (e * e').extend_domain f :=
extend_domain_trans _ _ _

/-- `extend_domain` as a group homomorphism -/
@[simps] def extend_domain_hom : perm α →* perm β :=
{ to_fun := λ e, extend_domain e f,
  map_one' := extend_domain_one f,
  map_mul' := λ e e', (extend_domain_mul f e e').symm }

lemma extend_domain_hom_injective : function.injective (extend_domain_hom f) :=
((extend_domain_hom f).injective_iff).mpr (λ e he, ext (λ x, f.injective (subtype.ext
  ((extend_domain_apply_image e f x).symm.trans (ext_iff.mp he (f x))))))

end extend_domain

/-- If the permutation `f` fixes the subtype `{x // p x}`, then this returns the permutation
  on `{x // p x}` induced by `f`. -/
def subtype_perm (f : perm α) {p : α → Prop} (h : ∀ x, p x ↔ p (f x)) : perm {x // p x} :=
⟨λ x, ⟨f x, (h _).1 x.2⟩, λ x, ⟨f⁻¹ x, (h (f⁻¹ x)).2 $ by simpa using x.2⟩,
  λ _, by simp only [perm.inv_apply_self, subtype.coe_eta, subtype.coe_mk],
  λ _, by simp only [perm.apply_inv_self, subtype.coe_eta, subtype.coe_mk]⟩

@[simp] lemma subtype_perm_apply (f : perm α) {p : α → Prop} (h : ∀ x, p x ↔ p (f x))
  (x : {x // p x}) : subtype_perm f h x = ⟨f x, (h _).1 x.2⟩ := rfl

@[simp] lemma subtype_perm_one (p : α → Prop) (h : ∀ x, p x ↔ p ((1 : perm α) x)) :
  @subtype_perm α 1 p h = 1 :=
equiv.ext $ λ ⟨_, _⟩, rfl

/-- The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points. -/
def of_subtype {p : α → Prop} [decidable_pred p] : perm (subtype p) →* perm α :=
{ to_fun := λ f,
  ⟨λ x, if h : p x then f ⟨x, h⟩ else x, λ x, if h : p x then f⁻¹ ⟨x, h⟩ else x,
  λ x, have h : ∀ h : p x, p (f ⟨x, h⟩), from λ h, (f ⟨x, h⟩).2,
    by { simp only [], split_ifs at *;
         simp only [perm.inv_apply_self, subtype.coe_eta, subtype.coe_mk, not_true, *] at * },
  λ x, have h : ∀ h : p x, p (f⁻¹ ⟨x, h⟩), from λ h, (f⁻¹ ⟨x, h⟩).2,
    by { simp only [], split_ifs at *;
         simp only [perm.apply_inv_self, subtype.coe_eta, subtype.coe_mk, not_true, *] at * }⟩,
  map_one' := begin ext, dsimp, split_ifs; refl, end,
  map_mul' := λ f g, equiv.ext $ λ x, begin
  by_cases h : p x,
  { have h₁ : p (f (g ⟨x, h⟩)), from (f (g ⟨x, h⟩)).2,
    have h₂ : p (g ⟨x, h⟩), from (g ⟨x, h⟩).2,
    simp only [h, h₂, coe_fn_mk, perm.mul_apply, dif_pos, subtype.coe_eta] },
  { simp only [h, coe_fn_mk, perm.mul_apply, dif_neg, not_false_iff] }
end }

lemma of_subtype_subtype_perm {f : perm α} {p : α → Prop} [decidable_pred p]
  (h₁ : ∀ x, p x ↔ p (f x)) (h₂ : ∀ x, f x ≠ x → p x) :
  of_subtype (subtype_perm f h₁) = f :=
equiv.ext $ λ x, begin
  rw [of_subtype, subtype_perm],
  by_cases hx : p x,
  { simp only [hx, coe_fn_mk, dif_pos, monoid_hom.coe_mk, subtype.coe_mk]},
  { haveI := classical.prop_decidable,
    simp only [hx, not_not.mp (mt (h₂ x) hx), coe_fn_mk, dif_neg, not_false_iff,
      monoid_hom.coe_mk] }
end

lemma of_subtype_apply_of_mem {p : α → Prop} [decidable_pred p]
  (f : perm (subtype p)) {x : α} (hx : p x) :
  of_subtype f x = f ⟨x, hx⟩ :=
dif_pos hx

@[simp] lemma of_subtype_apply_coe {p : α → Prop} [decidable_pred p]
  (f : perm (subtype p)) (x : subtype p)  :
  of_subtype f x = f x :=
subtype.cases_on x $ λ _, of_subtype_apply_of_mem f

lemma of_subtype_apply_of_not_mem {p : α → Prop} [decidable_pred p]
  (f : perm (subtype p)) {x : α} (hx : ¬ p x) :
  of_subtype f x = x :=
dif_neg hx

lemma mem_iff_of_subtype_apply_mem {p : α → Prop} [decidable_pred p]
  (f : perm (subtype p)) (x : α) :
  p x ↔ p ((of_subtype f : α → α) x) :=
if h : p x then by simpa only [of_subtype, h, coe_fn_mk, dif_pos, true_iff, monoid_hom.coe_mk]
  using (f ⟨x, h⟩).2
else by simp [h, of_subtype_apply_of_not_mem f h]

@[simp] lemma subtype_perm_of_subtype {p : α → Prop} [decidable_pred p] (f : perm (subtype p)) :
  subtype_perm (of_subtype f) (mem_iff_of_subtype_apply_mem f) = f :=
equiv.ext $ λ ⟨x, hx⟩, by { dsimp [subtype_perm, of_subtype],
  simp only [show p x, from hx, dif_pos, subtype.coe_eta] }

instance perm_unique {n : Type*} [unique n] : unique (equiv.perm n) :=
{ default := 1,
  uniq := λ σ, equiv.ext (λ i, subsingleton.elim _ _) }

@[simp] lemma default_perm {n : Type*} : default (equiv.perm n) = 1 := rfl

variables (e : perm α) (ι : α ↪ β)

open_locale classical

/-- Noncomputable version of `equiv.perm.via_fintype_embedding` that does not assume `fintype` -/
noncomputable def via_embedding : perm β :=
extend_domain e (of_injective ι.1 ι.2)

lemma via_embedding_apply (x : α) : e.via_embedding ι (ι x) = ι (e x) :=
extend_domain_apply_image e (of_injective ι.1 ι.2) x

lemma via_embedding_apply_of_not_mem (x : β) (hx : x ∉ _root_.set.range ι) :
  e.via_embedding ι x = x :=
extend_domain_apply_not_subtype e (of_injective ι.1 ι.2) hx

/-- `via_embedding` as a group homomorphism -/
noncomputable def via_embedding_hom : perm α →* perm β:=
extend_domain_hom (of_injective ι.1 ι.2)

lemma via_embedding_hom_apply : via_embedding_hom ι e = via_embedding e ι := rfl

lemma via_embedding_hom_injective : function.injective (via_embedding_hom ι) :=
extend_domain_hom_injective (of_injective ι.1 ι.2)

end perm

section swap
variables [decidable_eq α]

@[simp] lemma swap_inv (x y : α) : (swap x y)⁻¹ = swap x y := rfl

@[simp] lemma swap_mul_self (i j : α) : swap i j * swap i j = 1 := swap_swap i j

lemma swap_mul_eq_mul_swap (f : perm α) (x y : α) : swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y) :=
equiv.ext $ λ z, begin
  simp only [perm.mul_apply, swap_apply_def],
  split_ifs;
  simp only [perm.apply_inv_self, *, perm.eq_inv_iff_eq, eq_self_iff_true, not_true] at *
end

lemma mul_swap_eq_swap_mul (f : perm α) (x y : α) : f * swap x y = swap (f x) (f y) * f :=
by rw [swap_mul_eq_mul_swap, perm.inv_apply_self, perm.inv_apply_self]

lemma swap_apply_apply (f : perm α) (x y : α) : swap (f x) (f y) = f * swap x y * f⁻¹ :=
by rw [mul_swap_eq_swap_mul, mul_inv_cancel_right]

/-- Left-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
lemma swap_mul_self_mul (i j : α) (σ : perm α) : equiv.swap i j * (equiv.swap i j * σ) = σ :=
by rw [←mul_assoc, swap_mul_self, one_mul]

/-- Right-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
lemma mul_swap_mul_self (i j : α) (σ : perm α) : (σ * equiv.swap i j) * equiv.swap i j = σ :=
by rw [mul_assoc, swap_mul_self, mul_one]

/-- A stronger version of `mul_right_injective` -/
@[simp]
lemma swap_mul_involutive (i j : α) : function.involutive ((*) (equiv.swap i j)) :=
swap_mul_self_mul i j

/-- A stronger version of `mul_left_injective` -/
@[simp]
lemma mul_swap_involutive (i j : α) : function.involutive (* (equiv.swap i j)) :=
mul_swap_mul_self i j

@[simp] lemma swap_eq_one_iff {i j : α} : swap i j = (1 : perm α) ↔ i = j :=
swap_eq_refl_iff

lemma swap_mul_eq_iff {i j : α} {σ : perm α} : swap i j * σ = σ ↔ i = j :=
⟨(assume h, have swap_id : swap i j = 1 := mul_right_cancel (trans h (one_mul σ).symm),
  by {rw [←swap_apply_right i j, swap_id], refl}),
(assume h, by erw [h, swap_self, one_mul])⟩

lemma mul_swap_eq_iff {i j : α} {σ : perm α} : σ * swap i j = σ ↔ i = j :=
⟨(assume h, have swap_id : swap i j = 1 := mul_left_cancel (trans h (one_mul σ).symm),
  by {rw [←swap_apply_right i j, swap_id], refl}),
(assume h, by erw [h, swap_self, mul_one])⟩

lemma swap_mul_swap_mul_swap {x y z : α} (hwz: x ≠ y) (hxz : x ≠ z) :
  swap y z * swap x y * swap y z = swap z x :=
equiv.ext $ λ n, by { simp only [swap_apply_def, perm.mul_apply], split_ifs; cc }

end swap

end equiv
