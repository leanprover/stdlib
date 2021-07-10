/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.algebra.module
import linear_algebra.multilinear

/-!
# Continuous multilinear maps

We define continuous multilinear maps as maps from `Π(i : ι), M₁ i` to `M₂` which are multilinear
and continuous, by extending the space of multilinear maps with a continuity assumption.
Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type, and all these
spaces are also topological spaces.

## Main definitions

* `continuous_multilinear_map R M₁ M₂` is the space of continuous multilinear maps from
  `Π(i : ι), M₁ i` to `M₂`. We show that it is an `R`-module.

## Implementation notes

We mostly follow the API of multilinear maps.

## Notation

We introduce the notation `M [×n]→L[R] M'` for the space of continuous `n`-multilinear maps from
`M^n` to `M'`. This is a particular case of the general notion (where we allow varying dependent
types as the arguments of our continuous multilinear maps), but arguably the most important one,
especially when defining iterated derivatives.
-/

open function fin set
open_locale big_operators

universes u v w w₁ w₁' w₂ w₃ w₄
variables {R : Type u} {ι : Type v} {n : ℕ} {M : fin n.succ → Type w} {M₁ : ι → Type w₁}
  {M₁' : ι → Type w₁'} {M₂ : Type w₂} {M₃ : Type w₃} {M₄ : Type w₄} [decidable_eq ι]

/-- Continuous multilinear maps over the ring `R`, from `Πi, M₁ i` to `M₂` where `M₁ i` and `M₂`
are modules over `R` with a topological structure. In applications, there will be compatibility
conditions between the algebraic and the topological structures, but this is not needed for the
definition. -/
structure continuous_multilinear_map (R : Type u) {ι : Type v} (M₁ : ι → Type w₁) (M₂ : Type w₂)
  [decidable_eq ι] [semiring R] [∀i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
  [∀i, module R (M₁ i)] [module R M₂] [∀i, topological_space (M₁ i)] [topological_space M₂]
  extends multilinear_map R M₁ M₂ :=
(cont : continuous to_fun)

notation M `[×`:25 n `]→L[`:25 R `] ` M' := continuous_multilinear_map R (λ (i : fin n), M) M'

namespace continuous_multilinear_map

section semiring

variables [semiring R]
[Πi, add_comm_monoid (M i)] [Πi, add_comm_monoid (M₁ i)] [Πi, add_comm_monoid (M₁' i)]
  [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄] [Π i, module R (M i)]
  [Π i, module R (M₁ i)]  [Π i, module R (M₁' i)] [module R M₂]
  [module R M₃] [module R M₄]
  [Π i, topological_space (M i)] [Π i, topological_space (M₁ i)] [Π i, topological_space (M₁' i)]
  [topological_space M₂] [topological_space M₃] [topological_space M₄]
(f f' : continuous_multilinear_map R M₁ M₂)

instance : has_coe_to_fun (continuous_multilinear_map R M₁ M₂) :=
⟨_, λ f, f.to_multilinear_map.to_fun⟩

@[continuity] lemma coe_continuous : continuous (f : (Π i, M₁ i) → M₂) := f.cont

@[simp] lemma coe_coe : (f.to_multilinear_map : (Π i, M₁ i) → M₂) = f := rfl

theorem to_multilinear_map_inj :
  function.injective (continuous_multilinear_map.to_multilinear_map :
    continuous_multilinear_map R M₁ M₂ → multilinear_map R M₁ M₂)
| ⟨f, hf⟩ ⟨g, hg⟩ rfl := rfl

@[ext] theorem ext {f f' : continuous_multilinear_map R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
to_multilinear_map_inj $ multilinear_map.ext H

@[simp] lemma map_add (m : Πi, M₁ i) (i : ι) (x y : M₁ i) :
  f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
f.map_add' m i x y

@[simp] lemma map_smul (m : Πi, M₁ i) (i : ι) (c : R) (x : M₁ i) :
  f (update m i (c • x)) = c • f (update m i x) :=
f.map_smul' m i c x

lemma map_coord_zero {m : Πi, M₁ i} (i : ι) (h : m i = 0) : f m = 0 :=
f.to_multilinear_map.map_coord_zero i h

@[simp] lemma map_zero [nonempty ι] : f 0 = 0 :=
f.to_multilinear_map.map_zero

instance : has_zero (continuous_multilinear_map R M₁ M₂) :=
⟨{ cont := continuous_const, ..(0 : multilinear_map R M₁ M₂) }⟩

instance : inhabited (continuous_multilinear_map R M₁ M₂) := ⟨0⟩

@[simp] lemma zero_apply (m : Πi, M₁ i) : (0 : continuous_multilinear_map R M₁ M₂) m = 0 := rfl

section has_continuous_add
variable [has_continuous_add M₂]

instance : has_add (continuous_multilinear_map R M₁ M₂) :=
⟨λ f f', ⟨f.to_multilinear_map + f'.to_multilinear_map, f.cont.add f'.cont⟩⟩

@[simp] lemma add_apply (m : Πi, M₁ i) : (f + f') m = f m + f' m := rfl

@[simp] lemma to_multilinear_map_add (f g : continuous_multilinear_map R M₁ M₂) :
  (f + g).to_multilinear_map = f.to_multilinear_map + g.to_multilinear_map :=
rfl

instance add_comm_monoid : add_comm_monoid (continuous_multilinear_map R M₁ M₂) :=
to_multilinear_map_inj.add_comm_monoid _ rfl (λ _ _, rfl)

/-- Evaluation of a `continuous_multilinear_map` at a vector as an `add_monoid_hom`. -/
def apply_add_hom (m : Π i, M₁ i) : continuous_multilinear_map R M₁ M₂ →+ M₂ :=
⟨λ f, f m, rfl, λ _ _, rfl⟩

@[simp] lemma sum_apply {α : Type*} (f : α → continuous_multilinear_map R M₁ M₂)
  (m : Πi, M₁ i) {s : finset α} : (∑ a in s, f a) m = ∑ a in s, f a m :=
(apply_add_hom m).map_sum f s

end has_continuous_add

/-- If `f` is a continuous multilinear map, then `f.to_continuous_linear_map m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
def to_continuous_linear_map (m : Πi, M₁ i) (i : ι) : M₁ i →L[R] M₂ :=
{ cont := f.cont.comp (continuous_const.update i continuous_id),
  .. f.to_multilinear_map.to_linear_map m i }

/-- The cartesian product of two continuous multilinear maps, as a continuous multilinear map. -/
def prod (f : continuous_multilinear_map R M₁ M₂) (g : continuous_multilinear_map R M₁ M₃) :
  continuous_multilinear_map R M₁ (M₂ × M₃) :=
{ cont := f.cont.prod_mk g.cont,
  .. f.to_multilinear_map.prod g.to_multilinear_map }

@[simp] lemma prod_apply
  (f : continuous_multilinear_map R M₁ M₂) (g : continuous_multilinear_map R M₁ M₃) (m : Πi, M₁ i) :
  (f.prod g) m = (f m, g m) := rfl

/-- Combine a family of continuous multilinear maps with the same domain and codomains `M' i` into a
continuous multilinear map taking values in the space of functions `Π i, M' i`. -/
def pi {ι' : Type*} {M' : ι' → Type*} [Π i, add_comm_monoid (M' i)] [Π i, topological_space (M' i)]
  [Π i, module R (M' i)] (f : Π i, continuous_multilinear_map R M₁ (M' i)) :
  continuous_multilinear_map R M₁ (Π i, M' i) :=
{ cont := continuous_pi $ λ i, (f i).coe_continuous,
  to_multilinear_map := multilinear_map.pi (λ i, (f i).to_multilinear_map) }

@[simp] lemma coe_pi {ι' : Type*} {M' : ι' → Type*} [Π i, add_comm_monoid (M' i)]
  [Π i, topological_space (M' i)] [Π i, module R (M' i)]
  (f : Π i, continuous_multilinear_map R M₁ (M' i)) :
  ⇑(pi f) = λ m j, f j m :=
rfl

lemma pi_apply {ι' : Type*} {M' : ι' → Type*} [Π i, add_comm_monoid (M' i)]
  [Π i, topological_space (M' i)] [Π i, module R (M' i)]
  (f : Π i, continuous_multilinear_map R M₁ (M' i)) (m : Π i, M₁ i) (j : ι') :
  pi f m j = f j m :=
rfl

/-- If `g` is continuous multilinear and `f` is a collection of continuous linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a continuous multilinear map, that we call
`g.comp_continuous_linear_map f`. -/
def comp_continuous_linear_map
  (g : continuous_multilinear_map R M₁' M₄) (f : Π i : ι, M₁ i →L[R] M₁' i) :
  continuous_multilinear_map R M₁ M₄ :=
{ cont := g.cont.comp $ continuous_pi $ λj, (f j).cont.comp $ continuous_apply _,
  .. g.to_multilinear_map.comp_linear_map (λ i, (f i).to_linear_map) }

@[simp] lemma comp_continuous_linear_map_apply (g : continuous_multilinear_map R M₁' M₄)
  (f : Π i : ι, M₁ i →L[R] M₁' i) (m : Π i, M₁ i) :
  g.comp_continuous_linear_map f m = g (λ i, f i $ m i) :=
rfl

/-- Composing a continuous multilinear map with a continuous linear map gives again a
continuous multilinear map. -/
def _root_.continuous_linear_map.comp_continuous_multilinear_map
  (g : M₂ →L[R] M₃) (f : continuous_multilinear_map R M₁ M₂) :
  continuous_multilinear_map R M₁ M₃ :=
{ cont := g.cont.comp f.cont,
  .. g.to_linear_map.comp_multilinear_map f.to_multilinear_map }

@[simp] lemma _root_.continuous_linear_map.comp_continuous_multilinear_map_coe (g : M₂ →L[R] M₃)
  (f : continuous_multilinear_map R M₁ M₂) :
  ((g.comp_continuous_multilinear_map f) : (Πi, M₁ i) → M₃) =
  (g : M₂ → M₃) ∘ (f : (Πi, M₁ i) → M₂) :=
by { ext m, refl }


/-- `continuous_multilinear_map.pi` as an `equiv`. -/
@[simps]
def pi_equiv {ι' : Type*} {M' : ι' → Type*} [Π i, add_comm_monoid (M' i)]
  [Π i, topological_space (M' i)] [Π i, module R (M' i)] :
  (Π i, continuous_multilinear_map R M₁ (M' i)) ≃
  continuous_multilinear_map R M₁ (Π i, M' i) :=
{ to_fun := continuous_multilinear_map.pi,
  inv_fun := λ f i, (continuous_linear_map.proj i : _ →L[R] M' i).comp_continuous_multilinear_map f,
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl } }

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
additivity of a multilinear map along the first variable. -/
lemma cons_add (f : continuous_multilinear_map R M M₂) (m : Π(i : fin n), M i.succ) (x y : M 0) :
  f (cons (x+y) m) = f (cons x m) + f (cons y m) :=
f.to_multilinear_map.cons_add m x y

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of a multilinear map along the first variable. -/
lemma cons_smul
  (f : continuous_multilinear_map R M M₂) (m : Π(i : fin n), M i.succ) (c : R) (x : M 0) :
  f (cons (c • x) m) = c • f (cons x m) :=
f.to_multilinear_map.cons_smul m c x

lemma map_piecewise_add (m m' : Πi, M₁ i) (t : finset ι) :
  f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m') :=
f.to_multilinear_map.map_piecewise_add _ _ _

/-- Additivity of a continuous multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
lemma map_add_univ [fintype ι] (m m' : Πi, M₁ i) :
  f (m + m') = ∑ s : finset ι, f (s.piecewise m m') :=
f.to_multilinear_map.map_add_univ _ _

section apply_sum

open fintype finset

variables {α : ι → Type*} [fintype ι] (g : Π i, α i → M₁ i) (A : Π i, finset (α i))

/-- If `f` is continuous multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the
sum of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/

lemma map_sum_finset  :
  f (λ i, ∑ j in A i, g i j) = ∑ r in pi_finset A, f (λ i, g i (r i)) :=
f.to_multilinear_map.map_sum_finset _ _

/-- If `f` is continuous multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
lemma map_sum [∀ i, fintype (α i)] :
  f (λ i, ∑ j, g i j) = ∑ r : Π i, α i, f (λ i, g i (r i)) :=
f.to_multilinear_map.map_sum _

end apply_sum

section restrict_scalar

variables (R) {A : Type*} [semiring A] [has_scalar R A] [Π (i : ι), module A (M₁ i)]
  [module A M₂] [∀ i, is_scalar_tower R A (M₁ i)] [is_scalar_tower R A M₂]

/-- Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algebra over `R`
and their actions on all involved modules agree with the action of `R` on `A`. -/
def restrict_scalars (f : continuous_multilinear_map A M₁ M₂) :
  continuous_multilinear_map R M₁ M₂ :=
{ to_multilinear_map := f.to_multilinear_map.restrict_scalars R,
  cont := f.cont }

@[simp] lemma coe_restrict_scalars (f : continuous_multilinear_map A M₁ M₂) :
  ⇑(f.restrict_scalars R) = f := rfl

end restrict_scalar

end semiring

section ring

variables [ring R] [∀i, add_comm_group (M₁ i)] [add_comm_group M₂]
[∀i, module R (M₁ i)] [module R M₂] [∀i, topological_space (M₁ i)] [topological_space M₂]
(f f' : continuous_multilinear_map R M₁ M₂)

@[simp] lemma map_sub (m : Πi, M₁ i) (i : ι) (x y : M₁ i) :
  f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
f.to_multilinear_map.map_sub _ _ _ _

section topological_add_group
variable [topological_add_group M₂]

instance : has_neg (continuous_multilinear_map R M₁ M₂) :=
⟨λ f, {cont := f.cont.neg, ..(-f.to_multilinear_map)}⟩

@[simp] lemma neg_apply (m : Πi, M₁ i) : (-f) m = - (f m) := rfl

instance : has_sub (continuous_multilinear_map R M₁ M₂) :=
⟨λ f g, { cont := f.cont.sub g.cont, .. (f.to_multilinear_map - g.to_multilinear_map) }⟩

@[simp] lemma sub_apply (m : Πi, M₁ i) : (f - f') m = f m - f' m := rfl

instance : add_comm_group (continuous_multilinear_map R M₁ M₂) :=
to_multilinear_map_inj.add_comm_group _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)

end topological_add_group

end ring

section comm_semiring

variables [comm_semiring R]
[∀i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
[∀i, module R (M₁ i)] [module R M₂]
[∀i, topological_space (M₁ i)] [topological_space M₂]
(f : continuous_multilinear_map R M₁ M₂)

lemma map_piecewise_smul (c : ι → R) (m : Πi, M₁ i) (s : finset ι) :
  f (s.piecewise (λ i, c i • m i) m) = (∏ i in s, c i) • f m :=
f.to_multilinear_map.map_piecewise_smul _ _ _

/-- Multiplicativity of a continuous multilinear map along all coordinates at the same time,
writing `f (λ i, c i • m i)` as `(∏ i, c i) • f m`. -/
lemma map_smul_univ [fintype ι] (c : ι → R) (m : Πi, M₁ i) :
  f (λ i, c i • m i) = (∏ i, c i) • f m :=
f.to_multilinear_map.map_smul_univ _ _

variables {R' A : Type*} [comm_semiring R'] [semiring A] [algebra R' A]
  [Π i, module A (M₁ i)] [module R' M₂] [module A M₂] [is_scalar_tower R' A M₂]
  [topological_space R'] [has_continuous_smul R' M₂]

instance : has_scalar R' (continuous_multilinear_map A M₁ M₂) :=
⟨λ c f, { cont := continuous_const.smul f.cont, .. c • f.to_multilinear_map }⟩

@[simp] lemma smul_apply (f : continuous_multilinear_map A M₁ M₂) (c : R') (m : Πi, M₁ i) :
  (c • f) m = c • f m := rfl

@[simp] lemma to_multilinear_map_smul (c : R') (f : continuous_multilinear_map A M₁ M₂) :
  (c • f).to_multilinear_map = c • f.to_multilinear_map :=
rfl

instance {R''} [comm_semiring R''] [has_scalar R' R''] [algebra R'' A]
  [module R'' M₂] [is_scalar_tower R'' A M₂] [is_scalar_tower R' R'' M₂]
  [topological_space R''] [has_continuous_smul R'' M₂]:
  is_scalar_tower R' R'' (continuous_multilinear_map A M₁ M₂) :=
⟨λ c₁ c₂ f, ext $ λ x, smul_assoc _ _ _⟩

variable [has_continuous_add M₂]

/-- The space of continuous multilinear maps over an algebra over `R` is a module over `R`, for the
pointwise addition and scalar multiplication. -/
instance : module R' (continuous_multilinear_map A M₁ M₂) :=
{ one_smul := λ f, ext $ λ x, one_smul _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul _ _ _,
  smul_zero := λ r, ext $ λ x, smul_zero _,
  smul_add := λ r f₁ f₂, ext $ λ x, smul_add _ _ _,
  add_smul := λ r₁ r₂ f, ext $ λ x, add_smul _ _ _,
  zero_smul := λ f, ext $ λ x, zero_smul _ _ }

/-- Linear map version of the map `to_multilinear_map` associating to a continuous multilinear map
the corresponding multilinear map. -/
@[simps] def to_multilinear_map_linear :
  (continuous_multilinear_map A M₁ M₂) →ₗ[R'] (multilinear_map A M₁ M₂) :=
{ to_fun    := λ f, f.to_multilinear_map,
  map_add'  := λ f g, rfl,
  map_smul' := λ c f, rfl }

/-- `continuous_multilinear_map.pi` as a `linear_equiv`. -/
@[simps {simp_rhs := tt}]
def pi_linear_equiv {ι' : Type*} {M' : ι' → Type*}
  [Π i, add_comm_monoid (M' i)] [Π i, topological_space (M' i)] [∀ i, has_continuous_add (M' i)]
  [Π i, module R' (M' i)] [Π i, module A (M' i)] [∀ i, is_scalar_tower R' A (M' i)]
  [Π i, has_continuous_smul R' (M' i)] :
  -- typeclass search doesn't find this instance, presumably due to struggles converting
  -- `Π i, module R (M' i)` to `Π i, has_scalar R (M' i)` in dependent arguments.
  let inst : has_continuous_smul R' (Π i, M' i) := pi.has_continuous_smul in
  (Π i, continuous_multilinear_map A M₁ (M' i)) ≃ₗ[R']
    continuous_multilinear_map A M₁ (Π i, M' i) :=
{ map_add' := λ x y, rfl,
  map_smul' := λ c x, rfl,
  .. pi_equiv }

end comm_semiring

end continuous_multilinear_map
