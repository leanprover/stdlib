/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.equiv.basic
import algebra.group.basic
import algebra.group.hom
import algebra.group.pi
import algebra.group.prod
import logic.embedding

/-!
# The group of permutations (self-equivalences) of a type `α`

This file defines the `group` structure on `equiv.perm α`.
-/
universes u v

namespace equiv

variables {α : Type u} {β : Type v}

namespace perm

instance perm_group : group (perm α) :=
begin
  refine { mul := λ f g, equiv.trans g f,
           one := equiv.refl α,
           inv := equiv.symm,
           div_eq_mul_inv := λ _ _, rfl,
           ..};
  intros; apply equiv.ext; try { apply trans_apply },
  apply symm_apply_apply
end

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

lemma of_subtype_apply_of_not_mem {p : α → Prop} [decidable_pred p]
  (f : perm (subtype p)) {x : α} (hx : ¬ p x) :
  of_subtype f x = x :=
dif_neg hx

lemma of_subtype_apply_coe {p : α → Prop} [decidable_pred p]
  (f : perm (subtype p)) (x : subtype p) :
  of_subtype f ↑x = ↑(f x) :=
begin
  change dite _ _ _ = _,
  rw [dif_pos, subtype.coe_eta],
  exact x.2,
end

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

noncomputable def of_embedding : equiv.perm β :=
let ϕ := equiv.set.range ι ι.2 in equiv.perm.of_subtype
{ to_fun := λ x, ⟨ι (e (ϕ.symm x)), ⟨e.to_fun (ϕ.symm x), rfl⟩⟩,
  inv_fun := λ x, ⟨ι (e.symm (ϕ.symm x)), ⟨e.inv_fun (ϕ.symm x), rfl⟩⟩,
  left_inv := λ y, by
  { change ϕ (e.symm (ϕ.symm (ϕ (e (ϕ.symm y))))) = y,
    rw [ϕ.symm_apply_apply, e.symm_apply_apply, ϕ.apply_symm_apply] },
  right_inv := λ y, by
  { change ϕ (e (ϕ.symm (ϕ (e.symm (ϕ.symm y))))) = y,
    rw [ϕ.symm_apply_apply, e.apply_symm_apply, ϕ.apply_symm_apply] } }

lemma equiv.perm.of_embedding_apply (x : α) : e.of_embedding ι (ι x) = ι (e x) :=
begin
  dsimp only [equiv.perm.of_embedding],
  have key : ι x = ↑(⟨ι x, set.mem_range_self x⟩ : set.range ι) := rfl,
  rw [key, equiv.perm.of_subtype_apply_coe],
  change ↑(⟨_, _⟩ : set.range ι) = _,
  rw [subtype.coe_mk],
  congr,
  rw [equiv.symm_apply_eq, equiv.set.range_apply],
end

lemma equiv.perm.of_embedding_apply_of_not_mem (x : β)
  (hx : x ∉ set.range ι) : e.of_embedding ι x = x :=
equiv.perm.of_subtype_apply_of_not_mem _ hx

noncomputable def equiv.perm.of_embedding_map_homomorphism : (equiv.perm α) →* equiv.perm β:=
{ to_fun := λ e, equiv.perm.of_embedding e ι,
  map_one' := by
  { ext x,
    by_cases hx : x ∈ set.range ι,
    { obtain ⟨y, rfl⟩ := hx,
      exact equiv.perm.of_embedding_apply 1 ι y },
    { exact equiv.perm.of_embedding_apply_of_not_mem 1 ι x hx } },
  map_mul' := by
  { intros σ τ,
    ext x,
    by_cases hx : x ∈ set.range ι,
    { obtain ⟨y, rfl⟩ := hx,
      change _ = (σ.of_embedding ι)((τ.of_embedding ι)(ι y)),
      rw [equiv.perm.of_embedding_apply (σ * τ ) ι y,
          equiv.perm.of_embedding_apply τ ι y,
          equiv.perm.of_embedding_apply σ ι (τ y)],
      refl },
    { change _ = (σ.of_embedding ι)((τ.of_embedding ι) x),
      rw [equiv.perm.of_embedding_apply_of_not_mem (σ * τ) ι x hx,
          equiv.perm.of_embedding_apply_of_not_mem τ ι x hx,
          equiv.perm.of_embedding_apply_of_not_mem σ ι x hx] } } }

lemma equiv.perm_of_embedding_map_injective :
  function.injective (equiv.perm.of_embedding_map_homomorphism ι):=
(monoid_hom.injective_iff (equiv.perm.of_embedding_map_homomorphism ι)).2
  (λ σ σ_ker, equiv.perm.ext (λ x, ι.2 ((equiv.perm.of_embedding_apply σ ι x).symm.trans
    (equiv.ext_iff.1 σ_ker (ι.to_fun x)))))

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
