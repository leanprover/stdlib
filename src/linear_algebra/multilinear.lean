/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import linear_algebra.basic
import algebra.algebra.basic
import data.fintype.sort
import data.typeinfo

/-!
# Multilinear maps

We define multilinear maps as maps from `Π(i : ι), M₁ i` to `M₂` which are linear in each
coordinate. Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type
(although some statements will require it to be a fintype). This space, denoted by
`(Π i, M₁ i) →ₗₘ[R] M₂`, inherits a module structure by pointwise addition and multiplication.

## Main definitions

* `(Π i, M₁ i) →ₗₘ[R] M₂` is the space of multilinear maps from `Π(i : ι), M₁ i` to `M₂`.
* `f.map_smul` is the multiplicativity of the multilinear map `f` along each coordinate.
* `f.map_add` is the additivity of the multilinear map `f` along each coordinate.
* `f.map_smul_univ` expresses the multiplicativity of `f` over all coordinates at the same time,
  writing `f (λi, c i • m i)` as `(∏ i, c i) • f m`.
* `f.map_add_univ` expresses the additivity of `f` over all coordinates at the same time, writing
  `f (m + m')` as the sum over all subsets `s` of `ι` of `f (s.piecewise m m')`.
* `f.map_sum` expresses `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` as the sum of
  `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all possible functions.

We also register isomorphisms corresponding to currying or uncurrying variables, transforming a
multilinear function `f` on `n+1` variables into a linear function taking values in multilinear
functions in `n` variables, and into a multilinear function in `n` variables taking values in linear
functions. These operations are called `f.curry_left` and `f.curry_right` respectively
(with inverses `f.uncurry_left` and `f.uncurry_right`). These operations induce linear equivalences
between spaces of multilinear functions in `n+1` variables and spaces of linear functions into
multilinear functions in `n` variables (resp. multilinear functions in `n` variables taking values
in linear functions), called respectively `multilinear_curry_left_equiv` and
`multilinear_curry_right_equiv`.

## Notation

This introduces `V →ₗₘ[R] N` as notation for a multilinear map from `V` to `N`. Typically, this is
used as either `Π i, M i →ₗₘ[R] N` for dependently-typed arguments, and `(ι → M) →ₗₘ[R] N` for
non-dependently typed arguments.

This notation introduces some slight weirdness, as `Π i, M i →ₗₘ[R] N` is actually translated to
`multilinear_map R (typeinfo.pi_codomain (typeinfo.of $ Π i, M i)) N` instead of
`multilinear_map R M N`. These are defeq, but it is common to have to add `(_ : Π i, M i)`
elaboration hints to remind the elaborator of this fact.

## Implementation notes

Expressing that a map is linear along the `i`-th coordinate when all other coordinates are fixed
can be done in two (equivalent) different ways:
* fixing a vector `m : Π(j : ι - i), M₁ j.val`, and then choosing separately the `i`-th coordinate
* fixing a vector `m : Πj, M₁ j`, and then modifying its `i`-th coordinate
The second way is more artificial as the value of `m` at `i` is not relevant, but it has the
advantage of avoiding subtype inclusion issues. This is the definition we use, based on
`function.update` that allows to change the value of `m` at `i`.
-/

open function fin set
open_locale big_operators

universes u v v' v₁ v₂ v₃ w u'
variables {R : Type u} {ι : Type u'} {n : ℕ}
{M : fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}
[decidable_eq ι]

/-- Multilinear maps over the ring `R`, from `Πi, M₁ i` to `M₂` where `M₁ i` and `M₂` are modules
over `R`. -/
structure multilinear_map (R : Type u) {ι : Type u'} (M₁ : ι → Type v) (M₂ : Type w)
  [decidable_eq ι] [semiring R] [∀i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
  [∀i, semimodule R (M₁ i)] [semimodule R M₂] :=
(to_fun : (Πi, M₁ i) → M₂)
(map_add' : ∀(m : Πi, M₁ i) (i : ι) (x y : M₁ i),
  to_fun (update m i (x + y)) = to_fun (update m i x) + to_fun (update m i y))
(map_smul' : ∀(m : Πi, M₁ i) (i : ι) (c : R) (x : M₁ i),
  to_fun (update m i (c • x)) = c • to_fun (update m i x))

notation A ` →ₗₘ[`:25 R:25 `] ` N := multilinear_map R (typeinfo.pi_codomain (typeinfo.of A)) N

namespace multilinear_map

section semiring

variables [semiring R]
[∀i, add_comm_monoid (M i)] [∀i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [add_comm_monoid M₃]
[add_comm_monoid M']
[∀i, semimodule R (M i)] [∀i, semimodule R (M₁ i)] [semimodule R M₂] [semimodule R M₃]
[semimodule R M']
(f f' : (Π i, M₁ i) →ₗₘ[R] M₂)

instance : has_coe_to_fun ((Π i, M₁ i) →ₗₘ[R] M₂) := ⟨_, to_fun⟩

initialize_simps_projections multilinear_map (to_fun → apply)

@[simp] lemma to_fun_eq_coe : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : (Π i, M₁ i) → M₂) (h₁ h₂ ) :
  ⇑(⟨f, h₁, h₂⟩ : (Π i, M₁ i) →ₗₘ[R] M₂) = f := rfl

theorem congr_fun {f g : (Π i, M₁ i) →ₗₘ[R] M₂} (h : f = g) (x : Π i, M₁ i) : f x = g x :=
congr_arg (λ h : (Π i, M₁ i) →ₗₘ[R] M₂, h x) h

theorem congr_arg (f : (Π i, M₁ i) →ₗₘ[R] M₂) {x y : Π i, M₁ i} (h : x = y) : f x = f y :=
congr_arg (λ x : Π i, M₁ i, f x) h

theorem coe_inj ⦃f g : (Π i, M₁ i) →ₗₘ[R] M₂⦄ (h : ⇑f = g) : f = g :=
by cases f; cases g; cases h; refl

@[ext] theorem ext {f f' : (Π i, M₁ i) →ₗₘ[R] M₂} (H : ∀ x, f x = f' x) : f = f' :=
coe_inj (funext H)

theorem ext_iff {f g : (Π i, M₁ i) →ₗₘ[R] M₂} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

@[simp] lemma map_add (m : Πi, M₁ i) (i : ι) (x y : M₁ i) :
  f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
f.map_add' m i x y

@[simp] lemma map_smul (m : Πi, M₁ i) (i : ι) (c : R) (x : M₁ i) :
  f (update m i (c • x)) = c • f (update m i x) :=
f.map_smul' m i c x

lemma map_coord_zero {m : Πi, M₁ i} (i : ι) (h : m i = 0) : f m = 0 :=
begin
  have : (0 : R) • (0 : M₁ i) = 0, by simp,
  rw [← update_eq_self i m, h, ← this, f.map_smul, zero_smul]
end

@[simp] lemma map_update_zero (m : Πi, M₁ i) (i : ι) : f (update m i 0) = 0 :=
f.map_coord_zero i (update_same i 0 m)

@[simp] lemma map_zero [nonempty ι] : f 0 = 0 :=
begin
  obtain ⟨i, _⟩ : ∃i:ι, i ∈ set.univ := set.exists_mem_of_nonempty ι,
  exact map_coord_zero f i rfl
end

instance : has_add ((Π i, M₁ i) →ₗₘ[R] M₂) :=
⟨λf f', ⟨λx, f x + f' x, λm i x y, by simp [add_left_comm, add_assoc],
  λm i c x, by simp [smul_add]⟩⟩

@[simp] lemma add_apply (m : Πi, M₁ i) : (f + f') m = f m + f' m := rfl

instance : has_zero ((Π i, M₁ i) →ₗₘ[R] M₂) :=
⟨⟨λ _, 0, λm i x y, by simp, λm i c x, by simp⟩⟩

instance : inhabited ((Π i, M₁ i) →ₗₘ[R] M₂) := ⟨0⟩

@[simp] lemma zero_apply (m : Πi, M₁ i) : (0 : (Π i, M₁ i) →ₗₘ[R] M₂) m = 0 := rfl

instance : add_comm_monoid ((Π i, M₁ i) →ₗₘ[R] M₂) :=
by refine {zero := 0, add := (+), ..};
   intros; ext; simp [add_comm, add_left_comm]

@[simp] lemma sum_apply {α : Type*} (f : α → (Π i, M₁ i) →ₗₘ[R] M₂)
  (m : Πi, M₁ i) : ∀ {s : finset α}, (∑ a in s, f a) m = ∑ a in s, f a m :=
begin
  classical,
  apply finset.induction,
  { rw finset.sum_empty, simp },
  { assume a s has H, rw finset.sum_insert has, simp [H, has] }
end

/-- If `f` is a multilinear map, then `f.to_linear_map m i` is the linear map obtained by fixing all
coordinates but `i` equal to those of `m`, and varying the `i`-th coordinate. -/
def to_linear_map (m : Πi, M₁ i) (i : ι) : M₁ i →ₗ[R] M₂ :=
{ to_fun    := λx, f (update m i x),
  map_add'  := λx y, by simp,
  map_smul' := λc x, by simp }

/-- The cartesian product of two multilinear maps, as a multilinear map. -/
def prod (f : (Π i, M₁ i) →ₗₘ[R] M₂) (g : (Π i, M₁ i) →ₗₘ[R] M₃) :
  (Π i, M₁ i) →ₗₘ[R] (M₂ × M₃) :=
{ to_fun    := λ m, (f m, g m),
  map_add'  := λ m i x y, by simp,
  map_smul' := λ m i c x, by simp }

/-- Combine a family of multilinear maps with the same domain and codomains `M' i` into a
multilinear map taking values in the space of functions `Π i, M' i`. -/
@[simps] def pi {ι' : Type*} {M' : ι' → Type*} [Π i, add_comm_monoid (M' i)]
  [Π i, semimodule R (M' i)] (f : Π i, multilinear_map R M₁ (M' i)) :
  multilinear_map R M₁ (Π i, M' i) :=
{ to_fun := λ m i, f i m,
  map_add' := λ m i x y, funext $ λ j, (f j).map_add _ _ _ _,
  map_smul' := λ m i c x, funext $ λ j, (f j).map_smul _ _ _ _ }

/-- Given a multilinear map `f` on `n` variables (parameterized by `fin n`) and a subset `s` of `k`
of these variables, one gets a new multilinear map on `fin k` by varying these variables, and fixing
the other ones equal to a given value `z`. It is denoted by `f.restr s hk z`, where `hk` is a
proof that the cardinality of `s` is `k`. The implicit identification between `fin k` and `s` that
we use is the canonical (increasing) bijection. -/
def restr {k n : ℕ} (f : (fin n → M') →ₗₘ[R] M₂) (s : finset (fin n))
  (hk : s.card = k) (z : M') :
  (fin k → M') →ₗₘ[R] M₂ :=
{ to_fun    := λ v, f (λ j, if h : j ∈ s then v ((s.order_iso_of_fin hk).symm ⟨j, h⟩) else z),
  map_add'  := λ v i x y,
    by { erw [dite_comp_equiv_update, dite_comp_equiv_update, dite_comp_equiv_update], simp },
  map_smul' := λ v i c x, by { erw [dite_comp_equiv_update, dite_comp_equiv_update], simp } }
variable {R}

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the additivity of a
multilinear map along the first variable. -/
lemma cons_add (f : (Π i, M i) →ₗₘ[R] M₂) (m : Π(i : fin n), M i.succ) (x y : M 0) :
  f (cons (x+y) m) = f (cons x m) + f (cons y m) :=
by rw [← update_cons_zero x m (x+y), f.map_add, update_cons_zero, update_cons_zero]

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the multiplicativity
of a multilinear map along the first variable. -/
lemma cons_smul (f : (Π i, M i) →ₗₘ[R] M₂) (m : Π(i : fin n), M i.succ) (c : R) (x : M 0) :
  f (cons (c • x) m) = c • f (cons x m) :=
by rw [← update_cons_zero x m (c • x), f.map_smul, update_cons_zero]

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `snoc`, one can express directly the additivity of a
multilinear map along the first variable. -/
lemma snoc_add (f : (Π i, M i) →ₗₘ[R] M₂) (m : Π(i : fin n), M i.cast_succ) (x y : M (last n)) :
  f (snoc m (x+y)) = f (snoc m x) + f (snoc m y) :=
by rw [← update_snoc_last x m (x+y), f.map_add, update_snoc_last, update_snoc_last]

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the multiplicativity
of a multilinear map along the first variable. -/
lemma snoc_smul (f : (Π i, M i) →ₗₘ[R] M₂)
  (m : Π(i : fin n), M i.cast_succ) (c : R) (x : M (last n)) :
  f (snoc m (c • x)) = c • f (snoc m x) :=
by rw [← update_snoc_last x m (c • x), f.map_smul, update_snoc_last]

section

variables {M₁' : ι → Type*} [Π i, add_comm_monoid (M₁' i)] [Π i, semimodule R (M₁' i)]

/-- If `g` is a multilinear map and `f` is a collection of linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a multilinear map, that we call
`g.comp_linear_map f`. -/
def comp_linear_map (g : (Π i, M₁' i) →ₗₘ[R] M₂) (f : Π i, M₁ i →ₗ[R] M₁' i) :
  (Π i, M₁ i) →ₗₘ[R] M₂ :=
{ to_fun := λ m, g $ λ i, f i (m i),
  map_add' := λ m i x y,
    have ∀ j z, f j (update m i z j) = update (λ k, f k (m k)) i (f i z) j :=
      λ j z, function.apply_update (λ k, f k) _ _ _ _,
    by simp [this],
  map_smul' := λ m i c x,
    have ∀ j z, f j (update m i z j) = update (λ k, f k (m k)) i (f i z) j :=
      λ j z, function.apply_update (λ k, f k) _ _ _ _,
    by simp [this] }

@[simp] lemma comp_linear_map_apply (g : (Π i, M₁' i) →ₗₘ[R] M₂) (f : Π i, M₁ i →ₗ[R] M₁' i)
  (m : Π i, M₁ i) :
  g.comp_linear_map f m = g (λ i, f i (m i)) :=
rfl

end

/-- If one adds to a vector `m'` another vector `m`, but only for coordinates in a finset `t`, then
the image under a multilinear map `f` is the sum of `f (s.piecewise m m')` along all subsets `s` of
`t`. This is mainly an auxiliary statement to prove the result when `t = univ`, given in
`map_add_univ`, although it can be useful in its own right as it does not require the index set `ι`
to be finite.-/
lemma map_piecewise_add (m m' : Πi, M₁ i) (t : finset ι) :
  f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m') :=
begin
  revert m',
  refine finset.induction_on t (by simp) _,
  assume i t hit Hrec m',
  have A : (insert i t).piecewise (m + m') m' = update (t.piecewise (m + m') m') i (m i + m' i) :=
    t.piecewise_insert _ _ _,
  have B : update (t.piecewise (m + m') m') i (m' i) = t.piecewise (m + m') m',
  { ext j,
    by_cases h : j = i,
    { rw h, simp [hit] },
    { simp [h] } },
  let m'' := update m' i (m i),
  have C : update (t.piecewise (m + m') m') i (m i) = t.piecewise (m + m'') m'',
  { ext j,
    by_cases h : j = i,
    { rw h, simp [m'', hit] },
    { by_cases h' : j ∈ t; simp [h, hit, m'', h'] } },
  rw [A, f.map_add, B, C, finset.sum_powerset_insert hit, Hrec, Hrec, add_comm],
  congr' 1,
  apply finset.sum_congr rfl (λs hs, _),
  have : (insert i s).piecewise m m' = s.piecewise m m'',
  { ext j,
    by_cases h : j = i,
    { rw h, simp [m'', finset.not_mem_of_mem_powerset_of_not_mem hs hit] },
    { by_cases h' : j ∈ s; simp [h, m'', h'] } },
  rw this
end

/-- Additivity of a multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
lemma map_add_univ [fintype ι] (m m' : Πi, M₁ i) :
  f (m + m') = ∑ s : finset ι, f (s.piecewise m m') :=
by simpa using f.map_piecewise_add m m' finset.univ

section apply_sum

variables {α : ι → Type*} (g : Π i, α i → M₁ i) (A : Π i, finset (α i))

open_locale classical
open fintype finset

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. Here, we give an auxiliary statement tailored for an inductive proof. Use instead
`map_sum_finset`. -/
lemma map_sum_finset_aux [fintype ι] {n : ℕ} (h : ∑ i, (A i).card = n) :
  f (λ i, ∑ j in A i, g i j) = ∑ r in pi_finset A, f (λ i, g i (r i)) :=
begin
  induction n using nat.strong_induction_on with n IH generalizing A,
  -- If one of the sets is empty, then all the sums are zero
  by_cases Ai_empty : ∃ i, A i = ∅,
  { rcases Ai_empty with ⟨i, hi⟩,
    have : ∑ j in A i, g i j = 0, by convert sum_empty,
    rw f.map_coord_zero i this,
    have : pi_finset A = ∅,
    { apply finset.eq_empty_of_forall_not_mem (λ r hr, _),
      have : r i ∈ A i := mem_pi_finset.mp hr i,
      rwa hi at this },
    convert sum_empty.symm },
  push_neg at Ai_empty,
  -- Otherwise, if all sets are at most singletons, then they are exactly singletons and the result
  -- is again straightforward
  by_cases Ai_singleton : ∀ i, (A i).card ≤ 1,
  { have Ai_card : ∀ i, (A i).card = 1,
    { assume i,
      have pos : finset.card (A i) ≠ 0, by simp [finset.card_eq_zero, Ai_empty i],
      have : finset.card (A i) ≤ 1 := Ai_singleton i,
      exact le_antisymm this (nat.succ_le_of_lt (_root_.pos_iff_ne_zero.mpr pos)) },
    have : ∀ (r : Π i, α i), r ∈ pi_finset A → f (λ i, g i (r i)) = f (λ i, ∑ j in A i, g i j),
    { assume r hr,
      unfold_coes,
      congr' with i,
      have : ∀ j ∈ A i, g i j = g i (r i),
      { assume j hj,
        congr,
        apply finset.card_le_one_iff.1 (Ai_singleton i) hj,
        exact mem_pi_finset.mp hr i },
      simp only [finset.sum_congr rfl this, finset.mem_univ, finset.sum_const, Ai_card i,
                 one_nsmul] },
    simp only [sum_congr rfl this, Ai_card, card_pi_finset, prod_const_one, one_nsmul,
               sum_const] },
  -- Remains the interesting case where one of the `A i`, say `A i₀`, has cardinality at least 2.
  -- We will split into two parts `B i₀` and `C i₀` of smaller cardinality, let `B i = C i = A i`
  -- for `i ≠ i₀`, apply the inductive assumption to `B` and `C`, and add up the corresponding
  -- parts to get the sum for `A`.
  push_neg at Ai_singleton,
  obtain ⟨i₀, hi₀⟩ : ∃ i, 1 < (A i).card := Ai_singleton,
  obtain ⟨j₁, j₂, hj₁, hj₂, j₁_ne_j₂⟩ : ∃ j₁ j₂, (j₁ ∈ A i₀) ∧ (j₂ ∈ A i₀) ∧ j₁ ≠ j₂ :=
    finset.one_lt_card_iff.1 hi₀,
  let B := function.update A i₀ (A i₀ \ {j₂}),
  let C := function.update A i₀ {j₂},
  have B_subset_A : ∀ i, B i ⊆ A i,
  { assume i,
    by_cases hi : i = i₀,
    { rw hi, simp only [B, sdiff_subset, update_same]},
    { simp only [hi, B, update_noteq, ne.def, not_false_iff, finset.subset.refl] } },
  have C_subset_A : ∀ i, C i ⊆ A i,
  { assume i,
    by_cases hi : i = i₀,
    { rw hi, simp only [C, hj₂, finset.singleton_subset_iff, update_same] },
    { simp only [hi, C, update_noteq, ne.def, not_false_iff, finset.subset.refl] } },
  -- split the sum at `i₀` as the sum over `B i₀` plus the sum over `C i₀`, to use additivity.
  have A_eq_BC : (λ i, ∑ j in A i, g i j) =
    function.update (λ i, ∑ j in A i, g i j) i₀ (∑ j in B i₀, g i₀ j + ∑ j in C i₀, g i₀ j),
  { ext i,
    by_cases hi : i = i₀,
    { rw [hi],
      simp only [function.update_same],
      have : A i₀ = B i₀ ∪ C i₀,
      { simp only [B, C, function.update_same, finset.sdiff_union_self_eq_union],
        symmetry,
        simp only [hj₂, finset.singleton_subset_iff, union_eq_left_iff_subset] },
      rw this,
      apply finset.sum_union,
      apply finset.disjoint_right.2 (λ j hj, _),
      have : j = j₂, by { dsimp [C] at hj, simpa using hj },
      rw this,
      dsimp [B],
      simp only [mem_sdiff, eq_self_iff_true, not_true, not_false_iff, finset.mem_singleton,
                 update_same, and_false] },
    { simp [hi] } },
  have Beq : function.update (λ i, ∑ j in A i, g i j) i₀ (∑ j in B i₀, g i₀ j) =
    (λ i, ∑ j in B i, g i j),
  { ext i,
    by_cases hi : i = i₀,
    { rw hi, simp only [update_same] },
    { simp only [hi, B, update_noteq, ne.def, not_false_iff] } },
  have Ceq : function.update (λ i, ∑ j in A i, g i j) i₀ (∑ j in C i₀, g i₀ j) =
    (λ i, ∑ j in C i, g i j),
  { ext i,
    by_cases hi : i = i₀,
    { rw hi, simp only [update_same] },
    { simp only [hi, C, update_noteq, ne.def, not_false_iff] } },
  -- Express the inductive assumption for `B`
  have Brec : f (λ i, ∑ j in B i, g i j) = ∑ r in pi_finset B, f (λ i, g i (r i)),
  { have : ∑ i, finset.card (B i) < ∑ i, finset.card (A i),
    { refine finset.sum_lt_sum (λ i hi, finset.card_le_of_subset (B_subset_A i))
        ⟨i₀, finset.mem_univ _, _⟩,
      have : {j₂} ⊆ A i₀, by simp [hj₂],
      simp only [B, finset.card_sdiff this, function.update_same, finset.card_singleton],
      exact nat.pred_lt (ne_of_gt (lt_trans nat.zero_lt_one hi₀)) },
    rw h at this,
    exact IH _ this B rfl },
  -- Express the inductive assumption for `C`
  have Crec : f (λ i, ∑ j in C i, g i j) = ∑ r in pi_finset C, f (λ i, g i (r i)),
  { have : ∑ i, finset.card (C i) < ∑ i, finset.card (A i) :=
      finset.sum_lt_sum (λ i hi, finset.card_le_of_subset (C_subset_A i))
        ⟨i₀, finset.mem_univ _, by simp [C, hi₀]⟩,
    rw h at this,
    exact IH _ this C rfl },
  have D : disjoint (pi_finset B) (pi_finset C),
  { have : disjoint (B i₀) (C i₀), by simp [B, C],
    exact pi_finset_disjoint_of_disjoint B C this },
  have pi_BC : pi_finset A = pi_finset B ∪ pi_finset C,
  { apply finset.subset.antisymm,
    { assume r hr,
      by_cases hri₀ : r i₀ = j₂,
      { apply finset.mem_union_right,
        apply mem_pi_finset.2 (λ i, _),
        by_cases hi : i = i₀,
        { have : r i₀ ∈ C i₀, by simp [C, hri₀],
          convert this },
        { simp [C, hi, mem_pi_finset.1 hr i] } },
      { apply finset.mem_union_left,
        apply mem_pi_finset.2 (λ i, _),
        by_cases hi : i = i₀,
        { have : r i₀ ∈ B i₀,
            by simp [B, hri₀, mem_pi_finset.1 hr i₀],
          convert this },
        { simp [B, hi, mem_pi_finset.1 hr i] } } },
    { exact finset.union_subset (pi_finset_subset _ _ (λ i, B_subset_A i))
        (pi_finset_subset _ _ (λ i, C_subset_A i)) } },
  rw A_eq_BC,
  simp only [multilinear_map.map_add, Beq, Ceq, Brec, Crec, pi_BC],
  rw ← finset.sum_union D,
end

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
lemma map_sum_finset [fintype ι] :
  f (λ i, ∑ j in A i, g i j) = ∑ r in pi_finset A, f (λ i, g i (r i)) :=
f.map_sum_finset_aux _ _ rfl

/-- If `f` is multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
lemma map_sum [fintype ι] [∀ i, fintype (α i)] :
  f (λ i, ∑ j, g i j) = ∑ r : Π i, α i, f (λ i, g i (r i)) :=
f.map_sum_finset g (λ i, finset.univ)

lemma map_update_sum {α : Type*} (t : finset α) (i : ι) (g : α → M₁ i) (m : Π i, M₁ i):
  f (update m i (∑ a in t, g a)) = ∑ a in t, f (update m i (g a)) :=
begin
  induction t using finset.induction with a t has ih h,
  { simp },
  { simp [finset.sum_insert has, ih] }
end

end apply_sum

section restrict_scalar

variables (R) {A : Type*} [semiring A] [has_scalar R A] [Π (i : ι), semimodule A (M₁ i)]
  [semimodule A M₂] [∀ i, is_scalar_tower R A (M₁ i)] [is_scalar_tower R A M₂]

/-- Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algebra over `R`
and their actions on all involved semimodules agree with the action of `R` on `A`. -/
def restrict_scalars (f : multilinear_map A M₁ M₂) : (Π i, M₁ i) →ₗₘ[R] M₂ :=
{ to_fun := f,
  map_add' := f.map_add,
  map_smul' := λ m i, (f.to_linear_map m i).map_smul_of_tower }

@[simp] lemma coe_restrict_scalars (f : multilinear_map A M₁ M₂) :
  ⇑(f.restrict_scalars R) = f := rfl

end restrict_scalar


section

variables {ι₁ ι₂ ι₃ : Type*} [decidable_eq ι₁] [decidable_eq ι₂] [decidable_eq ι₃]

/-- Transfer the arguments to a map along an equivalence between argument indices.

The naming is derived from `finsupp.dom_congr`, noting that here the permutation applies to the
domain of the domain. -/
@[simps apply]
def dom_dom_congr (σ : ι₁ ≃ ι₂) (m : (ι₁ → M₂) →ₗₘ[R] M₃) : (ι₂ → M₂) →ₗₘ[R] M₃ :=
{ to_fun := λ v, m (λ i, v (σ i)),
  map_add' := λ (v : ι₂ → M₂) i a b, by {
    simp_rw function.update_apply_equiv_apply v, rw m.map_add, },
  map_smul' := λ (v : ι₂ → M₂) i a b, by {
    simp_rw function.update_apply_equiv_apply v, rw m.map_smul, }, }

lemma dom_dom_congr_trans (σ₁ : ι₁ ≃ ι₂) (σ₂ : ι₂ ≃ ι₃) (m : (ι₁ → M₂) →ₗₘ[R] M₃) :
  m.dom_dom_congr (σ₁.trans σ₂) = (m.dom_dom_congr σ₁).dom_dom_congr σ₂ := rfl

lemma dom_dom_congr_mul (σ₁ : equiv.perm ι₁) (σ₂ : equiv.perm ι₁)
  (m : (ι₁ → M₂) →ₗₘ[R] M₃) :
  m.dom_dom_congr (σ₂ * σ₁) = (m.dom_dom_congr σ₁).dom_dom_congr σ₂ := rfl

/-- `multilinear_map.dom_dom_congr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symm_apply]
def dom_dom_congr_equiv (σ : ι₁ ≃ ι₂) :
  ((ι₁ → M₂) →ₗₘ[R] M₃) ≃+ ((ι₂ → M₂) →ₗₘ[R] M₃) :=
{ to_fun := dom_dom_congr σ,
  inv_fun := dom_dom_congr σ.symm,
  left_inv := λ m, by {ext (x : ι₁ → M₂), simp},
  right_inv := λ m, by {ext (x : ι₂ → M₂), simp},
  map_add' := λ a b, by {ext, simp} }

end

end semiring

end multilinear_map

namespace linear_map
variables [semiring R]
[Πi, add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M']
[∀i, semimodule R (M₁ i)] [semimodule R M₂] [semimodule R M₃] [semimodule R M']

/-- Composing a multilinear map with a linear map gives again a multilinear map. -/
def comp_multilinear_map (g : M₂ →ₗ[R] M₃) (f : (Π i, M₁ i) →ₗₘ[R] M₂) : (Π i, M₁ i) →ₗₘ[R] M₃ :=
{ to_fun    := g ∘ f,
  map_add'  := λ m i x y, by simp,
  map_smul' := λ m i c x, by simp }

@[simp] lemma coe_comp_multilinear_map (g : M₂ →ₗ[R] M₃) (f : (Π i, M₁ i) →ₗₘ[R] M₂) :
  ⇑(g.comp_multilinear_map f) = g ∘ f := rfl

lemma comp_multilinear_map_apply (g : M₂ →ₗ[R] M₃) (f : (Π i, M₁ i) →ₗₘ[R] M₂) (m : Π i, M₁ i) :
  g.comp_multilinear_map f m = g (f m) := rfl

variables {ι₁ ι₂ : Type*} [decidable_eq ι₁] [decidable_eq ι₂]

@[simp] lemma comp_multilinear_map_dom_dom_congr (σ : ι₁ ≃ ι₂) (g : M₂ →ₗ[R] M₃)
  (f : (ι₁ → M') →ₗₘ[R] M₂) :
  (g.comp_multilinear_map f).dom_dom_congr σ = g.comp_multilinear_map (f.dom_dom_congr σ) :=
by { ext, simp }

end linear_map

namespace multilinear_map

section comm_semiring

variables [comm_semiring R] [∀i, add_comm_monoid (M₁ i)] [∀i, add_comm_monoid (M i)]
[add_comm_monoid M₂] [∀i, semimodule R (M i)] [∀i, semimodule R (M₁ i)] [semimodule R M₂]
(f f' : (Π i, M₁ i) →ₗₘ[R] M₂)

/-- If one multiplies by `c i` the coordinates in a finset `s`, then the image under a multilinear
map is multiplied by `∏ i in s, c i`. This is mainly an auxiliary statement to prove the result when
`s = univ`, given in `map_smul_univ`, although it can be useful in its own right as it does not
require the index set `ι` to be finite. -/
lemma map_piecewise_smul (c : ι → R) (m : Πi, M₁ i) (s : finset ι) :
  f (s.piecewise (λi, c i • m i) m) = (∏ i in s, c i) • f m :=
begin
  refine s.induction_on (by simp) _,
  assume j s j_not_mem_s Hrec,
  have A : function.update (s.piecewise (λi, c i • m i) m) j (m j) =
           s.piecewise (λi, c i • m i) m,
  { ext i,
    by_cases h : i = j,
    { rw h, simp [j_not_mem_s] },
    { simp [h] } },
  rw [s.piecewise_insert, f.map_smul, A, Hrec],
  simp [j_not_mem_s, mul_smul]
end

/-- Multiplicativity of a multilinear map along all coordinates at the same time,
writing `f (λi, c i • m i)` as `(∏ i, c i) • f m`. -/
lemma map_smul_univ [fintype ι] (c : ι → R) (m : Πi, M₁ i) :
  f (λi, c i • m i) = (∏ i, c i) • f m :=
by simpa using map_piecewise_smul f c m finset.univ

section distrib_mul_action

variables {R' A : Type*} [monoid R'] [semiring A]
  [Π i, semimodule A (M₁ i)] [distrib_mul_action R' M₂] [semimodule A M₂] [smul_comm_class A R' M₂]

instance : has_scalar R' (multilinear_map A M₁ M₂) := ⟨λ c f,
  ⟨λ m, c • f m, λm i x y, by simp [smul_add], λl i x d, by simp [←smul_comm x c] ⟩⟩

@[simp] lemma smul_apply (f : multilinear_map A M₁ M₂) (c : R') (m : Πi, M₁ i) :
  (c • f) m = c • f m := rfl

instance : distrib_mul_action R' (multilinear_map A M₁ M₂) :=
{ one_smul := λ f, ext $ λ x, one_smul _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul _ _ _,
  smul_zero := λ r, ext $ λ x, smul_zero _,
  smul_add := λ r f₁ f₂, ext $ λ x, smul_add _ _ _ }

end distrib_mul_action

section semimodule

variables {R' A : Type*} [semiring R'] [semiring A]
  [Π i, semimodule A (M₁ i)] [semimodule A M₂]
  [add_comm_monoid M₃] [semimodule R' M₃] [semimodule A M₃] [smul_comm_class A R' M₃]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance [semimodule R' M₂] [smul_comm_class A R' M₂] : semimodule R' (multilinear_map A M₁ M₂) :=
{ add_smul := λ r₁ r₂ f, ext $ λ x, add_smul _ _ _,
  zero_smul := λ f, ext $ λ x, zero_smul _ _ }

variables (M₂ M₃ R' A)

/-- `multilinear_map.dom_dom_congr` as a `linear_equiv`. -/
@[simps apply symm_apply]
def dom_dom_congr_linear_equiv {ι₁ ι₂} [decidable_eq ι₁] [decidable_eq ι₂] (σ : ι₁ ≃ ι₂) :
  multilinear_map A (λ i : ι₁, M₂) M₃ ≃ₗ[R'] multilinear_map A (λ i : ι₂, M₂) M₃ :=
{ map_smul' := λ c f, by { ext, simp },
  .. (dom_dom_congr_equiv σ : multilinear_map A (λ i : ι₁, M₂) M₃ ≃+
        multilinear_map A (λ i : ι₂, M₂) M₃) }

end semimodule

section dom_coprod

open_locale tensor_product

variables {ι₁ ι₂ ι₃ ι₄ : Type*}
variables [decidable_eq ι₁] [decidable_eq ι₂][decidable_eq ι₃] [decidable_eq ι₄]
variables {N₁ : Type*} [add_comm_monoid N₁] [semimodule R N₁]
variables {N₂ : Type*} [add_comm_monoid N₂] [semimodule R N₂]
variables {N : Type*} [add_comm_monoid N] [semimodule R N]

/-- Given two multilinear maps `(ι₁ → N) → N₁` and `(ι₂ → N) → N₂`, this produces the map
`(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂` by taking the coproduct of the domain and the tensor product
of the codomain.

This can be thought of as combining `equiv.sum_arrow_equiv_prod_arrow.symm` with
`tensor_product.map`, noting that the two operations can't be separated as the intermediate result
is not a `multilinear_map`.

While this can be generalized to work for dependent `Π i : ι₁, N'₁ i` instead of `ι₁ → N`, doing so
introduces `sum.elim N'₁ N'₂` types in the result which are difficult to work with and not defeq
to the simple case defined here. See [this zulip thread](
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Instances.20on.20.60sum.2Eelim.20A.20B.20i.60/near/218484619).
-/
@[simps apply]
def dom_coprod
  (a : (ι₁ → N) →ₗₘ[R] N₁) (b : (ι₂ → N) →ₗₘ[R] N₂) :
  (ι₁ ⊕ ι₂ → N) →ₗₘ[R] (N₁ ⊗[R] N₂) :=
{ to_fun := λ v, a (λ i, v (sum.inl i)) ⊗ₜ b (λ i, v (sum.inr i)),
  map_add' := λ (v : ι₁ ⊕ ι₂ → N) i p q,
    by cases i; simp [tensor_product.add_tmul, tensor_product.tmul_add],
  map_smul' := λ (v : ι₁ ⊕ ι₂ → N) i c p,
    by cases i; simp [tensor_product.smul_tmul', tensor_product.tmul_smul] }

/-- A more bundled version of `multilinear_map.dom_coprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def dom_coprod' :
  ((ι₁ → N) →ₗₘ[R] N₁) ⊗[R] ((ι₂ → N) →ₗₘ[R] N₂) →ₗ[R]
  (ι₁ ⊕ ι₂ → N) →ₗₘ[R] (N₁ ⊗[R] N₂) :=
tensor_product.lift $ linear_map.mk₂ R (dom_coprod)
  (λ m₁ m₂ n, by { ext, simp only [dom_coprod_apply, tensor_product.add_tmul, add_apply] })
  (λ c m n,   by { ext, simp only [dom_coprod_apply, tensor_product.smul_tmul', smul_apply] })
  (λ m n₁ n₂, by { ext, simp only [dom_coprod_apply, tensor_product.tmul_add, add_apply] })
  (λ c m n,   by { ext, simp only [dom_coprod_apply, tensor_product.tmul_smul, smul_apply] })

@[simp]
lemma dom_coprod'_apply
  (a : (ι₁ → N) →ₗₘ[R] N₁) (b : (ι₂ → N) →ₗₘ[R] N₂) :
  dom_coprod' (a ⊗ₜ[R] b) = dom_coprod a b := rfl

/-- When passed an `equiv.sum_congr`, `multilinear_map.dom_dom_congr` distributes over
`multilinear_map.dom_coprod`. -/
lemma dom_coprod_dom_dom_congr_sum_congr
  (a : (ι₁ → N) →ₗₘ[R] N₁) (b : (ι₂ → N) →ₗₘ[R] N₂)
  (σa : ι₁ ≃ ι₃) (σb : ι₂ ≃ ι₄) :
    (a.dom_coprod b).dom_dom_congr (σa.sum_congr σb) =
      (a.dom_dom_congr σa).dom_coprod (b.dom_dom_congr σb) := rfl

end dom_coprod

section

variables (R ι) (A : Type*) [comm_semiring A] [algebra R A] [fintype ι]

/-- Given an `R`-algebra `A`, `mk_pi_algebra` is the multilinear map on `A^ι` associating
to `m` the product of all the `m i`.

See also `multilinear_map.mk_pi_algebra_fin` for a version that works with a non-commutative
algebra `A` but requires `ι = fin n`. -/
protected def mk_pi_algebra : (ι → A) →ₗₘ[R] A :=
{ to_fun := λ m, ∏ i, m i,
  map_add' := λ m i x y, by simp [finset.prod_update_of_mem, add_mul],
  map_smul' := λ m i c x, by simp [finset.prod_update_of_mem] }

variables {R A ι}

@[simp] lemma mk_pi_algebra_apply (m : ι → A) :
  multilinear_map.mk_pi_algebra R ι A m = ∏ i, m i :=
rfl

end

section

variables (R n) (A : Type*) [semiring A] [algebra R A]

/-- Given an `R`-algebra `A`, `mk_pi_algebra_fin` is the multilinear map on `A^n` associating
to `m` the product of all the `m i`.

See also `multilinear_map.mk_pi_algebra` for a version that assumes `[comm_semiring A]` but works
for `A^ι` with any finite type `ι`. -/
protected def mk_pi_algebra_fin : (fin n → A) →ₗₘ[R] A :=
{ to_fun := λ (m : fin n → A), (list.of_fn m).prod,
  map_add' :=
    begin
      intros m i x y,
      have : (list.fin_range n).index_of i < n,
        by simpa using list.index_of_lt_length.2 (list.mem_fin_range i),
      simp [list.of_fn_eq_map, (list.nodup_fin_range n).map_update, list.prod_update_nth, add_mul,
        this, mul_add, add_mul]
    end,
  map_smul' :=
    begin
      intros m i c x,
      have : (list.fin_range n).index_of i < n,
        by simpa using list.index_of_lt_length.2 (list.mem_fin_range i),
      simp [list.of_fn_eq_map, (list.nodup_fin_range n).map_update, list.prod_update_nth, this]
    end }

variables {R A n}

@[simp] lemma mk_pi_algebra_fin_apply (m : fin n → A) :
  multilinear_map.mk_pi_algebra_fin R n A m = (list.of_fn m).prod :=
rfl

lemma mk_pi_algebra_fin_apply_const (a : A) :
  multilinear_map.mk_pi_algebra_fin R n A (λ _, a) = a ^ n :=
by simp

end

/-- Given an `R`-multilinear map `f` taking values in `R`, `f.smul_right z` is the map
sending `m` to `f m • z`. -/
def smul_right (f : (Π i, M₁ i) →ₗₘ[R] R) (z : M₂) : (Π i, M₁ i) →ₗₘ[R] M₂ :=
(linear_map.smul_right linear_map.id z).comp_multilinear_map f

@[simp] lemma smul_right_apply (f : (Π i, M₁ i) →ₗₘ[R] R) (z : M₂) (m : Π i, M₁ i) :
  f.smul_right z m = f m • z :=
rfl

variables (R ι)

/-- The canonical multilinear map on `R^ι` when `ι` is finite, associating to `m` the product of
all the `m i` (multiplied by a fixed reference element `z` in the target module). See also
`mk_pi_algebra` for a more general version. -/
protected def mk_pi_ring [fintype ι] (z : M₂) : (ι → R) →ₗₘ[R] M₂ :=
(multilinear_map.mk_pi_algebra R ι R).smul_right z

variables {R ι}

@[simp] lemma mk_pi_ring_apply [fintype ι] (z : M₂) (m : ι → R) :
  (multilinear_map.mk_pi_ring R ι z : (ι → R) → M₂) m = (∏ i, m i) • z := rfl

lemma mk_pi_ring_apply_one_eq_self [fintype ι]  (f : (ι → R) →ₗₘ[R] M₂) :
  multilinear_map.mk_pi_ring R ι (f (λi, 1)) = f :=
begin
  ext m,
  have : m = (λi, m i • 1), by { ext j, simp },
  conv_rhs { rw [this, f.map_smul_univ] },
  refl
end

end comm_semiring

section range_add_comm_group

variables [semiring R] [∀i, add_comm_monoid (M₁ i)] [add_comm_group M₂]
[∀i, semimodule R (M₁ i)] [semimodule R M₂]
(f g : (Π i, M₁ i) →ₗₘ[R] M₂)

instance : has_neg ((Π i, M₁ i) →ₗₘ[R] M₂) :=
⟨λ f, ⟨λ m, - f m, λm i x y, by simp [add_comm], λm i c x, by simp⟩⟩

@[simp] lemma neg_apply (m : Πi, M₁ i) : (-f) m = - (f m) := rfl

instance : has_sub ((Π i, M₁ i) →ₗₘ[R] M₂) :=
⟨λ f g,
  ⟨λ m, f m - g m,
   λ m i x y, by { simp only [map_add, sub_eq_add_neg, neg_add, add_add_add_comm], },
   λ m i c x, by { simp only [map_smul, smul_sub] }⟩⟩

@[simp] lemma sub_apply (m : Πi, M₁ i) : (f - g) m = f m - g m := rfl

instance : add_comm_group ((Π i, M₁ i) →ₗₘ[R] M₂) :=
by refine { zero := 0, add := (+), neg := has_neg.neg,
            sub := has_sub.sub, sub_eq_add_neg := _, .. };
   intros; ext; simp [add_comm, add_left_comm, sub_eq_add_neg]

end range_add_comm_group

section add_comm_group

variables [semiring R] [∀i, add_comm_group (M₁ i)] [add_comm_group M₂]
[∀i, semimodule R (M₁ i)] [semimodule R M₂]
(f : (Π i, M₁ i) →ₗₘ[R] M₂)

@[simp] lemma map_neg (m : Πi, M₁ i) (i : ι) (x : M₁ i) :
  f (update m i (-x)) = -f (update m i x) :=
eq_neg_of_add_eq_zero $ by rw [←map_add, add_left_neg, f.map_coord_zero i (update_same i 0 m)]

@[simp] lemma map_sub (m : Πi, M₁ i) (i : ι) (x y : M₁ i) :
  f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
by rw [sub_eq_add_neg, sub_eq_add_neg, map_add, map_neg]

end add_comm_group

section comm_semiring

variables [comm_semiring R] [∀i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
[∀i, semimodule R (M₁ i)] [semimodule R M₂]

/-- When `ι` is finite, multilinear maps on `R^ι` with values in `M₂` are in bijection with `M₂`,
as such a multilinear map is completely determined by its value on the constant vector made of ones.
We register this bijection as a linear equivalence in `multilinear_map.pi_ring_equiv`. -/
protected def pi_ring_equiv [fintype ι]  : M₂ ≃ₗ[R] ((ι → R) →ₗₘ[R] M₂) :=
{ to_fun    := λ z, multilinear_map.mk_pi_ring R ι z,
  inv_fun   := λ f, f (λi, 1),
  map_add'  := λ z z', by { ext m, simp [smul_add] },
  map_smul' := λ c z, by { ext m, simp [smul_smul, mul_comm] },
  left_inv  := λ z, by simp,
  right_inv := λ f, f.mk_pi_ring_apply_one_eq_self }

end comm_semiring

end multilinear_map

section currying
/-!
### Currying

We associate to a multilinear map in `n+1` variables (i.e., based on `fin n.succ`) two
curried functions, named `f.curry_left` (which is a linear map on `E 0` taking values
in multilinear maps in `n` variables) and `f.curry_right` (wich is a multilinear map in `n`
variables taking values in linear maps on `E 0`). In both constructions, the variable that is
singled out is `0`, to take advantage of the operations `cons` and `tail` on `fin n`.
The inverse operations are called `uncurry_left` and `uncurry_right`.

We also register linear equiv versions of these correspondences, in
`multilinear_curry_left_equiv` and `multilinear_curry_right_equiv`.
-/
open multilinear_map

variables {R M M₂}
[comm_semiring R] [∀i, add_comm_monoid (M i)] [add_comm_monoid M'] [add_comm_monoid M₂]
[∀i, semimodule R (M i)] [semimodule R M'] [semimodule R M₂]

/-! #### Left currying -/

/-- Given a linear map `f` from `M 0` to multilinear maps on `n` variables,
construct the corresponding multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)`-/
def linear_map.uncurry_left
  (f : M 0 →ₗ[R] ((Π (i : fin n), M i.succ) →ₗₘ[R] M₂)) :
  (Π i, M i) →ₗₘ[R] M₂ :=
{ to_fun := λm, f (m 0) (tail m),
  map_add' := λm i x y, begin
    by_cases h : i = 0,
    { subst i,
      rw [update_same, update_same, update_same, f.map_add, add_apply,
          tail_update_zero, tail_update_zero, tail_update_zero] },
    { rw [update_noteq (ne.symm h), update_noteq (ne.symm h), update_noteq (ne.symm h)],
      revert x y,
      rw ← succ_pred i h,
      assume x y,
      rw [tail_update_succ, map_add, tail_update_succ, tail_update_succ] }
  end,
  map_smul' := λm i c x, begin
    by_cases h : i = 0,
    { subst i,
      rw [update_same, update_same, tail_update_zero, tail_update_zero,
          ← smul_apply, f.map_smul] },
    { rw [update_noteq (ne.symm h), update_noteq (ne.symm h)],
      revert x,
      rw ← succ_pred i h,
      assume x,
      rw [tail_update_succ, tail_update_succ, map_smul] }
  end }

@[simp] lemma linear_map.uncurry_left_apply
  (f : M 0 →ₗ[R] ((Π i : fin n, M i.succ) →ₗₘ[R] M₂)) (m : Πi, M i) :
  f.uncurry_left m = f (m 0) (tail m) := rfl

/-- Given a multilinear map `f` in `n+1` variables, split the first variable to obtain
a linear map into multilinear maps in `n` variables, given by `x ↦ (m ↦ f (cons x m))`. -/
def multilinear_map.curry_left
  (f : (Π i, M i) →ₗₘ[R] M₂) :
  M 0 →ₗ[R] ((Π i : fin n, M i.succ) →ₗₘ[R] M₂) :=
{ to_fun := λx,
  { to_fun    := λm, f (cons x m),
    map_add'  := λm i y y', by simp,
    map_smul' := λm i y c, by simp },
  map_add' := λx y, by { ext m, exact cons_add f m x y },
  map_smul' := λc x, by { ext m, exact cons_smul f m c x } }

@[simp] lemma multilinear_map.curry_left_apply
  (f : (Π i, M i) →ₗₘ[R] M₂) (x : M 0) (m : Π(i : fin n), M i.succ) :
  f.curry_left x m = f (cons x m) := rfl

@[simp] lemma linear_map.curry_uncurry_left
  (f : M 0 →ₗ[R] ((Π i : fin n, M i.succ) →ₗₘ[R] M₂)) :
  f.uncurry_left.curry_left = f :=
begin
  ext m x,
  simp only [tail_cons, linear_map.uncurry_left_apply, multilinear_map.curry_left_apply],
  rw cons_zero
end

@[simp] lemma multilinear_map.uncurry_curry_left
  (f : (Π i, M i) →ₗₘ[R] M₂) :
  f.curry_left.uncurry_left = f :=
by { ext m, simp, }

variables (R M M₂)

/-- The space of multilinear maps on `Π(i : fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from `M 0` to the space of multilinear maps on
`Π(i : fin n), M i.succ `, by separating the first variable. We register this isomorphism as a
linear isomorphism in `multilinear_curry_left_equiv R M M₂`.

The direct and inverse maps are given by `f.uncurry_left` and `f.curry_left`. Use these
unless you need the full framework of linear equivs. -/
def multilinear_curry_left_equiv :
  (M 0 →ₗ[R] ((Π i : fin n, M i.succ) →ₗₘ[R] M₂)) ≃ₗ[R] ((Π i, M i) →ₗₘ[R] M₂) :=
{ to_fun    := linear_map.uncurry_left,
  map_add'  := λf₁ f₂, by { ext m, refl },
  map_smul' := λc f, by { ext m, refl },
  inv_fun   := multilinear_map.curry_left,
  left_inv  := linear_map.curry_uncurry_left,
  right_inv := multilinear_map.uncurry_curry_left }

variables {R M M₂}

/-! #### Right currying -/

/-- Given a multilinear map `f` in `n` variables to the space of linear maps from `M (last n)` to
`M₂`, construct the corresponding multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (init m) (m (last n))`-/
def multilinear_map.uncurry_right
  (f : ((Π i : fin n, M i.cast_succ) →ₗₘ[R] (M (last n) →ₗ[R] M₂))) :
  (Π i, M i) →ₗₘ[R] M₂ :=
{ to_fun := λm, f (init m) (m (last n)),
  map_add' := λm i x y, begin
    by_cases h : i.val < n,
    { have : last n ≠ i := ne.symm (ne_of_lt h),
      rw [update_noteq this, update_noteq this, update_noteq this],
      revert x y,
      rw  [(cast_succ_cast_lt i h).symm],
      assume x y,
      rw [init_update_cast_succ, map_add, init_update_cast_succ, init_update_cast_succ,
          linear_map.add_apply] },
    { revert x y,
      rw eq_last_of_not_lt h,
      assume x y,
      rw [init_update_last, init_update_last, init_update_last,
          update_same, update_same, update_same, linear_map.map_add] }
  end,
  map_smul' := λm i c x, begin
    by_cases h : i.val < n,
    { have : last n ≠ i := ne.symm (ne_of_lt h),
      rw [update_noteq this, update_noteq this],
      revert x,
      rw  [(cast_succ_cast_lt i h).symm],
      assume x,
      rw [init_update_cast_succ, init_update_cast_succ, map_smul, linear_map.smul_apply] },
    { revert x,
      rw eq_last_of_not_lt h,
      assume x,
      rw [update_same, update_same, init_update_last, init_update_last,
          linear_map.map_smul] }
  end }

@[simp] lemma multilinear_map.uncurry_right_apply
  (f : ((Π i : fin n, M i.cast_succ) →ₗₘ[R] ((M (last n)) →ₗ[R] M₂))) (m : Πi, M i) :
  f.uncurry_right m = f (init m) (m (last n)) := rfl

/-- Given a multilinear map `f` in `n+1` variables, split the last variable to obtain
a multilinear map in `n` variables taking values in linear maps from `M (last n)` to `M₂`, given by
`m ↦ (x ↦ f (snoc m x))`. -/
def multilinear_map.curry_right (f : (Π i, M i) →ₗₘ[R] M₂) :
  (Π i : fin n, M (fin.cast_succ i)) →ₗₘ[R] ((M (last n)) →ₗ[R] M₂) :=
{ to_fun := λm,
  { to_fun    := λx, f (snoc m x),
    map_add'  := λx y, by rw f.snoc_add,
    map_smul' := λc x, by rw f.snoc_smul },
  map_add' := λm i x y, begin
    ext z,
    change f (snoc (update m i (x + y)) z)
      = f (snoc (update m i x) z) + f (snoc (update m i y) z),
    rw [snoc_update, snoc_update, snoc_update, f.map_add]
  end,
  map_smul' := λm i c x, begin
    ext z,
    change f (snoc (update m i (c • x)) z) = c • f (snoc (update m i x) z),
    rw [snoc_update, snoc_update, f.map_smul]
  end }

@[simp] lemma multilinear_map.curry_right_apply
  (f : (Π i, M i) →ₗₘ[R] M₂) (m : Π(i : fin n), M i.cast_succ) (x : M (last n)) :
  f.curry_right m x = f (snoc m x) := rfl

@[simp] lemma multilinear_map.curry_uncurry_right
  (f : (Π i : fin n, M i.cast_succ) →ₗₘ[R] ((M (last n)) →ₗ[R] M₂)) :
  f.uncurry_right.curry_right = f :=
begin
  ext m x,
  simp only [snoc_last, multilinear_map.curry_right_apply, multilinear_map.uncurry_right_apply],
  rw init_snoc
end

@[simp] lemma multilinear_map.uncurry_curry_right
  (f : (Π i, M i) →ₗₘ[R] M₂) : f.curry_right.uncurry_right = f :=
by { ext m, simp }

variables (R M M₂)

/-- The space of multilinear maps on `Π(i : fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from the space of multilinear maps on `Π(i : fin n), M i.cast_succ` to the
space of linear maps on `M (last n)`, by separating the last variable. We register this isomorphism
as a linear isomorphism in `multilinear_curry_right_equiv R M M₂`.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of linear equivs. -/
def multilinear_curry_right_equiv :
  ((Π i : fin n, M i.cast_succ) →ₗₘ[R] ((M (last n)) →ₗ[R] M₂))
  ≃ₗ[R] ((Π i, M i) →ₗₘ[R] M₂) :=
{ to_fun    := multilinear_map.uncurry_right,
  map_add'  := λf₁ f₂, by { ext m, refl },
  map_smul' := λc f, by { ext m, rw [smul_apply], refl },
  inv_fun   := multilinear_map.curry_right,
  left_inv  := multilinear_map.curry_uncurry_right,
  right_inv := multilinear_map.uncurry_curry_right }

namespace multilinear_map

variables {ι' : Type*} [decidable_eq ι'] [decidable_eq (ι ⊕ ι')] {R M₂}

/-- A multilinear map on `Π i : ι ⊕ ι', M'` defines a multilinear map on `Π i : ι, M'`
taking values in the space of multilinear maps on `Π i : ι', M'`. -/
def curry_sum (f : (ι ⊕ ι' → M') →ₗₘ[R] M₂) :
  (ι → M') →ₗₘ[R] ((ι' → M') →ₗₘ[R] M₂) :=
{ to_fun := λ (u : ι → M'),
  { to_fun := λ (v : ι' → M'), f (sum.elim u v),
    map_add' := λ v i x y, by simp only [← sum.update_elim_inr, f.map_add],
    map_smul' := λ v i c x, by simp only [← sum.update_elim_inr, f.map_smul] },
  map_add' := λ u i x y, ext $ λ v,
    by simp only [multilinear_map.coe_mk, add_apply, ← sum.update_elim_inl, f.map_add],
  map_smul' := λ u i c x, ext $ λ v,
    by simp only [multilinear_map.coe_mk, smul_apply, ← sum.update_elim_inl, f.map_smul] }

@[simp] lemma curry_sum_apply (f : (ι ⊕ ι' → M') →ₗₘ[R] M₂)
  (u : ι → M') (v : ι' → M') :
  f.curry_sum u v = f (sum.elim u v) :=
rfl

/-- A multilinear map on `Π i : ι, M'` taking values in the space of multilinear maps
on `Π i : ι', M'` defines a multilinear map on `Π i : ι ⊕ ι', M'`. -/
def uncurry_sum (f : (ι → M') →ₗₘ[R] ((ι' → M') →ₗₘ[R] M₂)) :
  (ι ⊕ ι' → M') →ₗₘ[R] M₂ :=
{ to_fun := λ (u : ι ⊕ ι' → M'), f (u ∘ sum.inl) (u ∘ sum.inr),
  map_add' := λ u i x y, by cases i;
    simp only [map_add, add_apply, sum.update_inl_comp_inl, sum.update_inl_comp_inr,
      sum.update_inr_comp_inl, sum.update_inr_comp_inr],
  map_smul' := λ u i c x, by cases i;
    simp only [map_smul, smul_apply, sum.update_inl_comp_inl, sum.update_inl_comp_inr,
      sum.update_inr_comp_inl, sum.update_inr_comp_inr] }

@[simp] lemma uncurry_sum_aux_apply
  (f : (ι → M') →ₗₘ[R] ((ι' → M') →ₗₘ[R] M₂)) (u : ι ⊕ ι' → M') :
  f.uncurry_sum u = f (u ∘ sum.inl) (u ∘ sum.inr) :=
rfl

variables (ι ι' R M₂ M')

/-- Linear equivalence between the space of multilinear maps on `Π i : ι ⊕ ι', M'` and the space
of multilinear maps on `Π i : ι, M'` taking values in the space of multilinear maps
on `Π i : ι', M'`. -/
def curry_sum_equiv : ((ι ⊕ ι' → M') →ₗₘ[R] M₂) ≃ₗ[R]
   (ι → M') →ₗₘ[R] ((ι' → M') →ₗₘ[R] M₂) :=
{ to_fun := curry_sum,
  inv_fun := uncurry_sum,
  left_inv := λ f, ext $ λ u, by simp,
  right_inv := λ f, by { ext, simp },
  map_add' := λ f g, by { ext, refl },
  map_smul' := λ c f, by { ext, refl } }

variables {ι ι' R M₂ M'}

@[simp] lemma coe_curry_sum_equiv : ⇑(curry_sum_equiv R ι M₂ M' ι') = curry_sum := rfl

@[simp] lemma coe_curr_sum_equiv_symm : ⇑(curry_sum_equiv R ι M₂ M' ι').symm = uncurry_sum := rfl

variables (R M₂ M')

/-- If `s : finset (fin n)` is a finite set of cardinality `k` and its complement has cardinality
`l`, then the space of multilinear maps on `λ i : fin n, M'` is isomorphic to the space of
multilinear maps on `λ i : fin k, M'` taking values in the space of multilinear maps
on `λ i : fin l, M'`. -/
def curry_fin_finset {k l n : ℕ} {s : finset (fin n)} [decidable_pred (s : set (fin n))]
  (hk : s.card = k) (hl : sᶜ.card = l) :
  ((fin n → M') →ₗₘ[R] M₂) ≃ₗ[R] (fin k → M') →ₗₘ[R] ((fin l → M') →ₗₘ[R] M₂) :=
(dom_dom_congr_linear_equiv M' M₂ R R (fin_sum_equiv_of_finset hk hl).symm).trans
  (curry_sum_equiv R (fin k) M₂ M' (fin l))

variables {R M₂ M'}

@[simp]
lemma curry_fin_finset_apply {k l n : ℕ} {s : finset (fin n)} [decidable_pred (s : set (fin n))]
  (hk : s.card = k) (hl : sᶜ.card = l) (f : (fin n → M') →ₗₘ[R] M₂)
  (mk : fin k → M') (ml : fin l → M') :
  curry_fin_finset R M₂ M' hk hl f mk ml =
    f (λ i, sum.elim mk ml ((fin_sum_equiv_of_finset hk hl).symm i)) :=
rfl

@[simp] lemma curry_fin_finset_symm_apply {k l n : ℕ} {s : finset (fin n)}
  [decidable_pred (s : set (fin n))] (hk : s.card = k) (hl : sᶜ.card = l)
  (f : (fin k → M') →ₗₘ[R] ((fin l → M') →ₗₘ[R] M₂))
  (m : fin n → M') :
  (curry_fin_finset R M₂ M' hk hl).symm f m =
    f (λ i, m $ fin_sum_equiv_of_finset hk hl (sum.inl i))
      (λ i, m $ fin_sum_equiv_of_finset hk hl (sum.inr i)) :=
rfl

@[simp] lemma curry_fin_finset_symm_apply_piecewise_const {k l n : ℕ} {s : finset (fin n)}
  [decidable_pred (s : set (fin n))] (hk : s.card = k) (hl : sᶜ.card = l)
  (f : (fin k → M') →ₗₘ[R] ((fin l → M') →ₗₘ[R] M₂)) (x y : M') :
  (curry_fin_finset R M₂ M' hk hl).symm f (s.piecewise (λ _, x) (λ _, y)) = f (λ _, x) (λ _, y) :=
begin
  rw curry_fin_finset_symm_apply, congr,
  { ext i, rw [fin_sum_equiv_of_finset_inl, finset.piecewise_eq_of_mem],
    apply finset.order_emb_of_fin_mem },
  { ext i, rw [fin_sum_equiv_of_finset_inr, finset.piecewise_eq_of_not_mem],
    exact finset.mem_compl.1 (finset.order_emb_of_fin_mem _ _ _) }
end

@[simp] lemma curry_fin_finset_symm_apply_const {k l n : ℕ} {s : finset (fin n)}
  [decidable_pred (s : set (fin n))] (hk : s.card = k) (hl : sᶜ.card = l)
  (f : (fin k → M') →ₗₘ[R] ((fin l → M') →ₗₘ[R] M₂)) (x : M') :
  (curry_fin_finset R M₂ M' hk hl).symm f (λ _, x) = f (λ _, x) (λ _, x) :=
rfl

@[simp] lemma curry_fin_finset_apply_const {k l n : ℕ} {s : finset (fin n)}
  [decidable_pred (s : set (fin n))]
  (hk : s.card = k) (hl : sᶜ.card = l) (f : (fin n → M') →ₗₘ[R] M₂) (x y : M') :
  curry_fin_finset R M₂ M' hk hl f (λ _, x) (λ _, y) = f (s.piecewise (λ _, x) (λ _, y)) :=
begin
  refine (curry_fin_finset_symm_apply_piecewise_const hk hl _ _ _).symm.trans _, -- `rw` fails
  rw linear_equiv.symm_apply_apply
end

end multilinear_map

end currying

section submodule

variables {R M M₂}
[ring R] [∀i, add_comm_monoid (M₁ i)] [add_comm_monoid M'] [add_comm_monoid M₂]
[∀i, semimodule R (M₁ i)] [semimodule R M'] [semimodule R M₂]

namespace multilinear_map

/-- The pushforward of an indexed collection of submodule `p i ⊆ M₁ i` by `f : M₁ → M₂`.

Note that this is not a submodule - it is not closed under addition. -/
def map [nonempty ι] (f : (Π i, M₁ i) →ₗₘ[R] M₂) (p : Π i, submodule R (M₁ i)) :
  sub_mul_action R M₂ :=
{ carrier   := f '' { v | ∀ i, v i ∈ p i},
  smul_mem' := λ c _ ⟨x, hx, hf⟩, let ⟨i⟩ := ‹nonempty ι› in by {
    refine ⟨update x i (c • x i), λ j, if hij : j = i then _ else _, hf ▸ _⟩,
    { rw [hij, update_same], exact (p i).smul_mem _ (hx i) },
    { rw [update_noteq hij], exact hx j },
    { rw [f.map_smul, update_eq_self] } } }

/-- The map is always nonempty. This lemma is needed to apply `sub_mul_action.zero_mem`. -/
lemma map_nonempty [nonempty ι] (f : (Π i, M₁ i) →ₗₘ[R] M₂) (p : Π i, submodule R (M₁ i)) :
  (map f p : set M₂).nonempty :=
⟨f 0, 0, λ i, (p i).zero_mem, rfl⟩

/-- The range of a multilinear map, closed under scalar multiplication. -/
def range [nonempty ι] (f : (Π i, M₁ i) →ₗₘ[R] M₂) : sub_mul_action R M₂ :=
f.map (λ i, ⊤)

end multilinear_map

end submodule
