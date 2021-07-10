/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johan Commelin
-/
import analysis.analytic.basic
import combinatorics.composition

/-!
# Composition of analytic functions

in this file we prove that the composition of analytic functions is analytic.

The argument is the following. Assume `g z = ∑' qₙ (z, ..., z)` and `f y = ∑' pₖ (y, ..., y)`. Then

`g (f y) = ∑' qₙ (∑' pₖ (y, ..., y), ..., ∑' pₖ (y, ..., y))
= ∑' qₙ (p_{i₁} (y, ..., y), ..., p_{iₙ} (y, ..., y))`.

For each `n` and `i₁, ..., iₙ`, define a `i₁ + ... + iₙ` multilinear function mapping
`(y₀, ..., y_{i₁ + ... + iₙ - 1})` to
`qₙ (p_{i₁} (y₀, ..., y_{i₁-1}), p_{i₂} (y_{i₁}, ..., y_{i₁ + i₂ - 1}), ..., p_{iₙ} (....)))`.
Then `g ∘ f` is obtained by summing all these multilinear functions.

To formalize this, we use compositions of an integer `N`, i.e., its decompositions into
a sum `i₁ + ... + iₙ` of positive integers. Given such a composition `c` and two formal
multilinear series `q` and `p`, let `q.comp_along_composition p c` be the above multilinear
function. Then the `N`-th coefficient in the power series expansion of `g ∘ f` is the sum of these
terms over all `c : composition N`.

To complete the proof, we need to show that this power series has a positive radius of convergence.
This follows from the fact that `composition N` has cardinality `2^(N-1)` and estimates on
the norm of `qₙ` and `pₖ`, which give summability. We also need to show that it indeed converges to
`g ∘ f`. For this, we note that the composition of partial sums converges to `g ∘ f`, and that it
corresponds to a part of the whole sum, on a subset that increases to the whole space. By
summability of the norms, this implies the overall convergence.

## Main results

* `q.comp p` is the formal composition of the formal multilinear series `q` and `p`.
* `has_fpower_series_at.comp` states that if two functions `g` and `f` admit power series expansions
  `q` and `p`, then `g ∘ f` admits a power series expansion given by `q.comp p`.
* `analytic_at.comp` states that the composition of analytic functions is analytic.
* `formal_multilinear_series.comp_assoc` states that composition is associative on formal
  multilinear series.

## Implementation details

The main technical difficulty is to write down things. In particular, we need to define precisely
`q.comp_along_composition p c` and to show that it is indeed a continuous multilinear
function. This requires a whole interface built on the class `composition`. Once this is set,
the main difficulty is to reorder the sums, writing the composition of the partial sums as a sum
over some subset of `Σ n, composition n`. We need to check that the reordering is a bijection,
running over difficulties due to the dependent nature of the types under consideration, that are
controlled thanks to the interface for `composition`.

The associativity of composition on formal multilinear series is a nontrivial result: it does not
follow from the associativity of composition of analytic functions, as there is no uniqueness for
the formal multilinear series representing a function (and also, it holds even when the radius of
convergence of the series is `0`). Instead, we give a direct proof, which amounts to reordering
double sums in a careful way. The change of variables is a canonical (combinatorial) bijection
`composition.sigma_equiv_sigma_pi` between `(Σ (a : composition n), composition a.length)` and
`(Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i))`, and is described
in more details below in the paragraph on associativity.
-/

noncomputable theory

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]
{H : Type*} [normed_group H] [normed_space 𝕜 H]

open filter list
open_locale topological_space big_operators classical nnreal ennreal

/-! ### Composing formal multilinear series -/

namespace formal_multilinear_series

/-!
In this paragraph, we define the composition of formal multilinear series, by summing over all
possible compositions of `n`.
-/

/-- Given a formal multilinear series `p`, a composition `c` of `n` and the index `i` of a
block of `c`, we may define a function on `fin n → E` by picking the variables in the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. This function is
called `p.apply_composition c v i` for `v : fin n → E` and `i : fin c.length`. -/
def apply_composition
  (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (c : composition n) :
  (fin n → E) → (fin (c.length) → F) :=
λ v i, p (c.blocks_fun i) (v ∘ (c.embedding i))

lemma apply_composition_ones (p : formal_multilinear_series 𝕜 E F) (n : ℕ) :
  p.apply_composition (composition.ones n) =
    λ v i, p 1 (λ _, v (fin.cast_le (composition.length_le _) i)) :=
begin
  funext v i,
  apply p.congr (composition.ones_blocks_fun _ _),
  intros j hjn hj1,
  obtain rfl : j = 0, { linarith },
  refine congr_arg v _,
  rw [fin.ext_iff, fin.coe_cast_le, composition.ones_embedding, fin.coe_mk],
end

lemma apply_composition_single (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (hn : 0 < n)
  (v : fin n → E) : p.apply_composition (composition.single n hn) v = λ j, p n v :=
begin
  ext j,
  refine p.congr (by simp) (λ i hi1 hi2, _),
  dsimp,
  congr' 1,
  convert composition.single_embedding hn ⟨i, hi2⟩,
  cases j,
  have : j_val = 0 := le_bot_iff.1 (nat.lt_succ_iff.1 j_property),
  unfold_coes,
  congr; try { assumption <|> simp },
end

@[simp] lemma remove_zero_apply_composition
  (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (c : composition n) :
  p.remove_zero.apply_composition c = p.apply_composition c :=
begin
  ext v i,
  simp [apply_composition, zero_lt_one.trans_le (c.one_le_blocks_fun i), remove_zero_of_pos],
end

/-- Technical lemma stating how `p.apply_composition` commutes with updating variables. This
will be the key point to show that functions constructed from `apply_composition` retain
multilinearity. -/
lemma apply_composition_update
  (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (c : composition n)
  (j : fin n) (v : fin n → E) (z : E) :
  p.apply_composition c (function.update v j z) =
    function.update (p.apply_composition c v) (c.index j)
      (p (c.blocks_fun (c.index j))
        (function.update (v ∘ (c.embedding (c.index j))) (c.inv_embedding j) z)) :=
begin
  ext k,
  by_cases h : k = c.index j,
  { rw h,
    let r : fin (c.blocks_fun (c.index j)) → fin n := c.embedding (c.index j),
    simp only [function.update_same],
    change p (c.blocks_fun (c.index j)) ((function.update v j z) ∘ r) = _,
    let j' := c.inv_embedding j,
    suffices B : (function.update v j z) ∘ r = function.update (v ∘ r) j' z,
      by rw B,
    suffices C : (function.update v (r j') z) ∘ r = function.update (v ∘ r) j' z,
      by { convert C, exact (c.embedding_comp_inv j).symm },
    exact function.update_comp_eq_of_injective _ (c.embedding _).injective _ _ },
  { simp only [h, function.update_eq_self, function.update_noteq, ne.def, not_false_iff],
    let r : fin (c.blocks_fun k) → fin n := c.embedding k,
    change p (c.blocks_fun k) ((function.update v j z) ∘ r) = p (c.blocks_fun k) (v ∘ r),
    suffices B : (function.update v j z) ∘ r = v ∘ r, by rw B,
    apply function.update_comp_eq_of_not_mem_range,
    rwa c.mem_range_embedding_iff' }
end

@[simp] lemma comp_continuous_linear_map_apply_composition {n : ℕ}
  (p : formal_multilinear_series 𝕜 F G) (f : E →L[𝕜] F) (c : composition n) (v : fin n → E) :
  (p.comp_continuous_linear_map f).apply_composition c v = p.apply_composition c (f ∘ v) :=
by simp [apply_composition]

end formal_multilinear_series

namespace continuous_multilinear_map
open formal_multilinear_series

/-- Given a formal multilinear series `p`, a composition `c` of `n` and a continuous multilinear
map `f` in `c.length` variables, one may form a multilinear map in `n` variables by applying
the right coefficient of `p` to each block of the composition, and then applying `f` to the
resulting vector. It is called `f.comp_along_composition_aux p c`.
This function admits a version as a continuous multilinear map, called
`f.comp_along_composition p c` below. -/
def comp_along_composition_aux {n : ℕ}
  (p : formal_multilinear_series 𝕜 E F) (c : composition n)
  (f : continuous_multilinear_map 𝕜 (λ (i : fin c.length), F) G) :
  multilinear_map 𝕜 (λ i : fin n, E) G :=
{ to_fun    := λ v, f (p.apply_composition c v),
  map_add'  := λ v i x y, by simp only [apply_composition_update,
    continuous_multilinear_map.map_add],
  map_smul' := λ v i c x, by simp only [apply_composition_update,
    continuous_multilinear_map.map_smul] }

/-- The norm of `f.comp_along_composition_aux p c` is controlled by the product of
the norms of the relevant bits of `f` and `p`. -/
lemma comp_along_composition_aux_bound {n : ℕ}
  (p : formal_multilinear_series 𝕜 E F) (c : composition n)
  (f : continuous_multilinear_map 𝕜 (λ (i : fin c.length), F) G) (v : fin n → E) :
  ∥f.comp_along_composition_aux p c v∥ ≤
    ∥f∥ * (∏ i, ∥p (c.blocks_fun i)∥) * (∏ i : fin n, ∥v i∥) :=
calc ∥f.comp_along_composition_aux p c v∥ = ∥f (p.apply_composition c v)∥ : rfl
... ≤ ∥f∥ * ∏ i, ∥p.apply_composition c v i∥ : continuous_multilinear_map.le_op_norm _ _
... ≤ ∥f∥ * ∏ i, ∥p (c.blocks_fun i)∥ *
        ∏ j : fin (c.blocks_fun i), ∥(v ∘ (c.embedding i)) j∥ :
  begin
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
    refine finset.prod_le_prod (λ i hi, norm_nonneg _) (λ i hi, _),
    apply continuous_multilinear_map.le_op_norm,
  end
... = ∥f∥ * (∏ i, ∥p (c.blocks_fun i)∥) *
        ∏ i (j : fin (c.blocks_fun i)), ∥(v ∘ (c.embedding i)) j∥ :
  by rw [finset.prod_mul_distrib, mul_assoc]
... = ∥f∥ * (∏ i, ∥p (c.blocks_fun i)∥) * (∏ i : fin n, ∥v i∥) :
  by { rw [← c.blocks_fin_equiv.prod_comp, ← finset.univ_sigma_univ, finset.prod_sigma],
       congr }

/-- Given a formal multilinear series `p`, a composition `c` of `n` and a continuous multilinear
map `f` in `c.length` variables, one may form a continuous multilinear map in `n` variables by
applying the right coefficient of `p` to each block of the composition, and then applying `f` to
the resulting vector. It is called `f.comp_along_composition p c`. It is constructed from the
analogous multilinear function `f.comp_along_composition_aux p c`, together with a norm
control to get the continuity. -/
def comp_along_composition {n : ℕ}
  (p : formal_multilinear_series 𝕜 E F) (c : composition n)
  (f : continuous_multilinear_map 𝕜 (λ (i : fin c.length), F) G) :
  continuous_multilinear_map 𝕜 (λ i : fin n, E) G :=
(f.comp_along_composition_aux p c).mk_continuous _
  (f.comp_along_composition_aux_bound p c)

@[simp] lemma comp_along_composition_apply {n : ℕ}
  (p : formal_multilinear_series 𝕜 E F) (c : composition n)
  (f : continuous_multilinear_map 𝕜 (λ (i : fin c.length), F) G) (v : fin n → E) :
  (f.comp_along_composition p c) v = f (p.apply_composition c v) := rfl

end continuous_multilinear_map

namespace formal_multilinear_series

/-- Given two formal multilinear series `q` and `p` and a composition `c` of `n`, one may
form a continuous multilinear map in `n` variables by applying the right coefficient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector. It is
called `q.comp_along_composition p c`. It is constructed from the analogous multilinear
function `q.comp_along_composition_aux p c`, together with a norm control to get
the continuity. -/
def comp_along_composition {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (c : composition n) : continuous_multilinear_map 𝕜 (λ i : fin n, E) G :=
(q c.length).comp_along_composition p c

@[simp] lemma comp_along_composition_apply {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (c : composition n) (v : fin n → E) :
  (q.comp_along_composition p c) v = q c.length (p.apply_composition c v) := rfl

/-- The norm of `q.comp_along_composition p c` is controlled by the product of
the norms of the relevant bits of `q` and `p`. -/
lemma comp_along_composition_norm {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (c : composition n) :
  ∥q.comp_along_composition p c∥ ≤ ∥q c.length∥ * ∏ i, ∥p (c.blocks_fun i)∥ :=
multilinear_map.mk_continuous_norm_le _
  (mul_nonneg (norm_nonneg _) (finset.prod_nonneg (λ i hi, norm_nonneg _))) _

lemma comp_along_composition_nnnorm {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (c : composition n) :
  nnnorm (q.comp_along_composition p c) ≤ nnnorm (q c.length) * ∏ i, nnnorm (p (c.blocks_fun i)) :=
by { rw ← nnreal.coe_le_coe, push_cast, exact q.comp_along_composition_norm p c }

/-- Formal composition of two formal multilinear series. The `n`-th coefficient in the composition
is defined to be the sum of `q.comp_along_composition p c` over all compositions of
`n`. In other words, this term (as a multilinear function applied to `v_0, ..., v_{n-1}`) is
`∑'_{k} ∑'_{i₁ + ... + iₖ = n} pₖ (q_{i_1} (...), ..., q_{i_k} (...))`, where one puts all variables
`v_0, ..., v_{n-1}` in increasing order in the dots.

In general, the composition `q ∘ p` only makes sense when the constant coefficient of `p` vanishes.
We give a general formula but which ignores the value of `p 0` instead.
-/
protected def comp (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F) :
  formal_multilinear_series 𝕜 E G :=
λ n, ∑ c : composition n, q.comp_along_composition p c

/-- The `0`-th coefficient of `q.comp p` is `q 0`. Since these maps are multilinear maps in zero
variables, but on different spaces, we can not state this directly, so we state it when applied to
arbitrary vectors (which have to be the zero vector). -/
lemma comp_coeff_zero (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (v : fin 0 → E) (v' : fin 0 → F) :
  (q.comp p) 0 v = q 0 v' :=
begin
  let c : composition 0 := composition.ones 0,
  dsimp [formal_multilinear_series.comp],
  have : {c} = (finset.univ : finset (composition 0)),
  { apply finset.eq_of_subset_of_card_le; simp [finset.card_univ, composition_card 0] },
  rw [← this, finset.sum_singleton, comp_along_composition_apply],
  symmetry, congr'
end

@[simp] lemma comp_coeff_zero'
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F) (v : fin 0 → E) :
  (q.comp p) 0 v = q 0 (λ i, 0) :=
q.comp_coeff_zero p v _

/-- The `0`-th coefficient of `q.comp p` is `q 0`. When `p` goes from `E` to `E`, this can be
expressed as a direct equality -/
lemma comp_coeff_zero'' (q : formal_multilinear_series 𝕜 E F)
  (p : formal_multilinear_series 𝕜 E E) :
  (q.comp p) 0 = q 0 :=
by { ext v, exact q.comp_coeff_zero p _ _ }

/-- The first coefficient of a composition of formal multilinear series is the composition of the
first coefficients seen as continuous linear maps. -/
lemma comp_coeff_one (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (v : fin 1 → E) : (q.comp p) 1 v = q 1 (λ i, p 1 v) :=
begin
  have : {composition.ones 1} = (finset.univ : finset (composition 1)) :=
    finset.eq_univ_of_card _ (by simp [composition_card]),
  simp only [formal_multilinear_series.comp, comp_along_composition_apply, ← this,
    finset.sum_singleton],
  refine q.congr (by simp) (λ i hi1 hi2, _),
  simp only [apply_composition_ones],
  exact p.congr rfl (λ j hj1 hj2, by congr)
end

lemma remove_zero_comp_of_pos (q : formal_multilinear_series 𝕜 F G)
  (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (hn : 0 < n) :
  q.remove_zero.comp p n = q.comp p n :=
begin
  ext v,
  simp only [formal_multilinear_series.comp, comp_along_composition,
    continuous_multilinear_map.comp_along_composition_apply, continuous_multilinear_map.sum_apply],
  apply finset.sum_congr rfl (λ c hc, _),
  rw remove_zero_of_pos _ (c.length_pos_of_pos hn)
end

@[simp] lemma comp_remove_zero (q : formal_multilinear_series 𝕜 F G)
  (p : formal_multilinear_series 𝕜 E F) :
  q.comp p.remove_zero = q.comp p :=
by { ext n, simp [formal_multilinear_series.comp] }

/-!
### The identity formal power series

We will now define the identity power series, and show that it is a neutral element for left and
right composition.
-/

section
variables (𝕜 E)

/-- The identity formal multilinear series, with all coefficients equal to `0` except for `n = 1`
where it is (the continuous multilinear version of) the identity. -/
def id : formal_multilinear_series 𝕜 E E
| 0 := 0
| 1 := (continuous_multilinear_curry_fin1 𝕜 E E).symm (continuous_linear_map.id 𝕜 E)
| _ := 0

/-- The first coefficient of `id 𝕜 E` is the identity. -/
@[simp] lemma id_apply_one (v : fin 1 → E) : (formal_multilinear_series.id 𝕜 E) 1 v = v 0 := rfl

/-- The `n`th coefficient of `id 𝕜 E` is the identity when `n = 1`. We state this in a dependent
way, as it will often appear in this form. -/
lemma id_apply_one' {n : ℕ} (h : n = 1) (v : fin n → E) :
  (id 𝕜 E) n v = v ⟨0, h.symm ▸ zero_lt_one⟩ :=
begin
  subst n,
  apply id_apply_one
end

/-- For `n ≠ 1`, the `n`-th coefficient of `id 𝕜 E` is zero, by definition. -/
@[simp] lemma id_apply_ne_one {n : ℕ} (h : n ≠ 1) : (formal_multilinear_series.id 𝕜 E) n = 0 :=
by { cases n, { refl }, cases n, { contradiction }, refl }

end

@[simp] theorem comp_id (p : formal_multilinear_series 𝕜 E F) : p.comp (id 𝕜 E) = p :=
begin
  ext1 n,
  dsimp [formal_multilinear_series.comp],
  rw finset.sum_eq_single (composition.ones n),
  show comp_along_composition p (id 𝕜 E) (composition.ones n) = p n,
  { ext v,
    rw comp_along_composition_apply,
    apply p.congr (composition.ones_length n),
    intros,
    rw apply_composition_ones,
    refine congr_arg v _,
    rw [fin.ext_iff, fin.coe_cast_le, fin.coe_mk, fin.coe_mk], },
  show ∀ (b : composition n),
    b ∈ finset.univ → b ≠ composition.ones n → comp_along_composition p (id 𝕜 E) b = 0,
  { assume b _ hb,
    obtain ⟨k, hk, lt_k⟩ : ∃ (k : ℕ) (H : k ∈ composition.blocks b), 1 < k :=
      composition.ne_ones_iff.1 hb,
    obtain ⟨i, i_lt, hi⟩ : ∃ (i : ℕ) (h : i < b.blocks.length), b.blocks.nth_le i h = k :=
      nth_le_of_mem hk,
    let j : fin b.length := ⟨i, b.blocks_length ▸ i_lt⟩,
    have A : 1 < b.blocks_fun j := by convert lt_k,
    ext v,
    rw [comp_along_composition_apply, continuous_multilinear_map.zero_apply],
    apply continuous_multilinear_map.map_coord_zero _ j,
    dsimp [apply_composition],
    rw id_apply_ne_one _ _ (ne_of_gt A),
    refl },
  { simp }
end

@[simp] theorem id_comp (p : formal_multilinear_series 𝕜 E F) (h : p 0 = 0) : (id 𝕜 F).comp p = p :=
begin
  ext1 n,
  by_cases hn : n = 0,
  { rw [hn, h],
    ext v,
    rw [comp_coeff_zero', id_apply_ne_one _ _ zero_ne_one],
    refl },
  { dsimp [formal_multilinear_series.comp],
    have n_pos : 0 < n := bot_lt_iff_ne_bot.mpr hn,
    rw finset.sum_eq_single (composition.single n n_pos),
    show comp_along_composition (id 𝕜 F) p (composition.single n n_pos) = p n,
    { ext v,
      rw [comp_along_composition_apply, id_apply_one' _ _ (composition.single_length n_pos)],
      dsimp [apply_composition],
      refine p.congr rfl (λ i him hin, congr_arg v $ _),
      ext, simp },
    show ∀ (b : composition n),
      b ∈ finset.univ → b ≠ composition.single n n_pos → comp_along_composition (id 𝕜 F) p b = 0,
    { assume b _ hb,
      have A : b.length ≠ 1, by simpa [composition.eq_single_iff_length] using hb,
      ext v,
      rw [comp_along_composition_apply, id_apply_ne_one _ _ A],
      refl },
    { simp } }
end

/-! ### Summability properties of the composition of formal power series-/
section

-- this speeds up the proof below a lot, related to leanprover-community/lean#521
local attribute [-instance] unique.subsingleton

/-- If two formal multilinear series have positive radius of convergence, then the terms appearing
in the definition of their composition are also summable (when multiplied by a suitable positive
geometric term). -/
theorem comp_summable_nnreal
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (hq : 0 < q.radius) (hp : 0 < p.radius) :
  ∃ r > (0 : ℝ≥0),
    summable (λ i : Σ n, composition n, nnnorm (q.comp_along_composition p i.2) * r ^ i.1) :=
begin
  /- This follows from the fact that the growth rate of `∥qₙ∥` and `∥pₙ∥` is at most geometric,
  giving a geometric bound on each `∥q.comp_along_composition p op∥`, together with the
  fact that there are `2^(n-1)` compositions of `n`, giving at most a geometric loss. -/
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 (lt_min ennreal.zero_lt_one hq) with ⟨rq, rq_pos, hrq⟩,
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 (lt_min ennreal.zero_lt_one hp) with ⟨rp, rp_pos, hrp⟩,
  simp only [lt_min_iff, ennreal.coe_lt_one_iff, ennreal.coe_pos] at hrp hrq rp_pos rq_pos,
  obtain ⟨Cq, hCq0, hCq⟩ : ∃ Cq > 0, ∀ n, nnnorm (q n) * rq^n ≤ Cq :=
    q.nnnorm_mul_pow_le_of_lt_radius hrq.2,
  obtain ⟨Cp, hCp1, hCp⟩ : ∃ Cp ≥ 1, ∀ n, nnnorm (p n) * rp^n ≤ Cp,
  { rcases p.nnnorm_mul_pow_le_of_lt_radius hrp.2 with ⟨Cp, -, hCp⟩,
    exact ⟨max Cp 1, le_max_right _ _, λ n, (hCp n).trans (le_max_left _ _)⟩ },
  let r0 : ℝ≥0 := (4 * Cp)⁻¹,
  have r0_pos : 0 < r0 := nnreal.inv_pos.2 (mul_pos zero_lt_four (zero_lt_one.trans_le hCp1)),
  set r : ℝ≥0 := rp * rq * r0,
  have r_pos : 0 < r := mul_pos (mul_pos rp_pos rq_pos) r0_pos,
  have I : ∀ (i : Σ (n : ℕ), composition n),
    nnnorm (q.comp_along_composition p i.2) * r ^ i.1 ≤ Cq / 4 ^ i.1,
  { rintros ⟨n, c⟩,
    have A,
    calc nnnorm (q c.length) * rq ^ n ≤ nnnorm (q c.length)* rq ^ c.length :
      mul_le_mul' le_rfl (pow_le_pow_of_le_one rq.2 hrq.1.le c.length_le)
    ... ≤ Cq : hCq _,
    have B,
    calc ((∏ i, nnnorm (p (c.blocks_fun i))) * rp ^ n)
        = ∏ i, nnnorm (p (c.blocks_fun i)) * rp ^ c.blocks_fun i :
      by simp only [finset.prod_mul_distrib, finset.prod_pow_eq_pow_sum, c.sum_blocks_fun]
    ... ≤ ∏ i : fin c.length, Cp : finset.prod_le_prod' (λ i _, hCp _)
    ... = Cp ^ c.length : by simp
    ... ≤ Cp ^ n : pow_le_pow hCp1 c.length_le,
    calc nnnorm (q.comp_along_composition p c) * r ^ n
        ≤ (nnnorm (q c.length) * ∏ i, nnnorm (p (c.blocks_fun i))) * r ^ n :
          mul_le_mul' (q.comp_along_composition_nnnorm p c) le_rfl
    ... = (nnnorm (q c.length) * rq ^ n) * ((∏ i, nnnorm (p (c.blocks_fun i))) * rp ^ n) * r0 ^ n :
          by { simp only [r, mul_pow], ac_refl }
    ... ≤ Cq * Cp ^ n * r0 ^ n : mul_le_mul' (mul_le_mul' A B) le_rfl
    ... = Cq / 4 ^ n :
      begin
        simp only [r0],
        field_simp [mul_pow, (zero_lt_one.trans_le hCp1).ne'],
        ac_refl
      end },
  refine ⟨r, r_pos, nnreal.summable_of_le I _⟩,
  simp_rw div_eq_mul_inv,
  refine summable.mul_left _ _,
  have : ∀ n : ℕ, has_sum (λ c : composition n, (4 ^ n : ℝ≥0)⁻¹) (2 ^ (n - 1) / 4 ^ n),
  { intro n,
    convert has_sum_fintype (λ c : composition n, (4 ^ n : ℝ≥0)⁻¹),
    simp [finset.card_univ, composition_card, div_eq_mul_inv] },
  refine nnreal.summable_sigma.2 ⟨λ n, (this n).summable, (nnreal.summable_nat_add_iff 1).1 _⟩,
  convert (nnreal.summable_geometric (nnreal.div_lt_one_of_lt one_lt_two)).mul_left (1 / 4),
  ext1 n,
  rw [(this _).tsum_eq, nat.add_sub_cancel],
  field_simp [← mul_assoc, pow_succ', mul_pow, show (4 : ℝ≥0) = 2 * 2, from (two_mul 2).symm,
    mul_right_comm]
end

end

/-- Bounding below the radius of the composition of two formal multilinear series assuming
summability over all compositions. -/
theorem le_comp_radius_of_summable
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F) (r : ℝ≥0)
  (hr : summable (λ i : (Σ n, composition n), nnnorm (q.comp_along_composition p i.2) * r ^ i.1)) :
  (r : ℝ≥0∞) ≤ (q.comp p).radius :=
begin
  refine le_radius_of_bound_nnreal _
    (∑' i : (Σ n, composition n), nnnorm (comp_along_composition q p i.snd) * r ^ i.fst) (λ n, _),
  calc nnnorm (formal_multilinear_series.comp q p n) * r ^ n ≤
  ∑' (c : composition n), nnnorm (comp_along_composition q p c) * r ^ n :
    begin
      rw [tsum_fintype, ← finset.sum_mul],
      exact mul_le_mul' (nnnorm_sum_le _ _) le_rfl
    end
  ... ≤ ∑' (i : Σ (n : ℕ), composition n), nnnorm (comp_along_composition q p i.snd) * r ^ i.fst :
    nnreal.tsum_comp_le_tsum_of_inj hr sigma_mk_injective
end

/-!
### Composing analytic functions

Now, we will prove that the composition of the partial sums of `q` and `p` up to order `N` is
given by a sum over some large subset of `Σ n, composition n` of `q.comp_along_composition p`, to
deduce that the series for `q.comp p` indeed converges to `g ∘ f` when `q` is a power series for
`g` and `p` is a power series for `f`.

This proof is a big reindexing argument of a sum. Since it is a bit involved, we define first
the source of the change of variables (`comp_partial_source`), its target
(`comp_partial_target`) and the change of variables itself (`comp_change_of_variables`) before
giving the main statement in `comp_partial_sum`. -/


/-- Source set in the change of variables to compute the composition of partial sums of formal
power series.
See also `comp_partial_sum`. -/
def comp_partial_sum_source (m M N : ℕ) : finset (Σ n, (fin n) → ℕ) :=
finset.sigma (finset.Ico m M) (λ (n : ℕ), fintype.pi_finset (λ (i : fin n), finset.Ico 1 N) : _)

@[simp] lemma mem_comp_partial_sum_source_iff (m M N : ℕ) (i : Σ n, (fin n) → ℕ) :
  i ∈ comp_partial_sum_source m M N ↔
    (m ≤ i.1 ∧ i.1 < M) ∧ ∀ (a : fin i.1), 1 ≤ i.2 a ∧ i.2 a < N :=
by simp only [comp_partial_sum_source, finset.Ico.mem, fintype.mem_pi_finset, finset.mem_sigma,
  iff_self]

/-- Change of variables appearing to compute the composition of partial sums of formal
power series -/
def comp_change_of_variables (m M N : ℕ) (i : Σ n, (fin n) → ℕ)
  (hi : i ∈ comp_partial_sum_source m M N) : (Σ n, composition n) :=
begin
  rcases i with ⟨n, f⟩,
  rw mem_comp_partial_sum_source_iff at hi,
  refine ⟨∑ j, f j, of_fn (λ a, f a), λ i hi', _, by simp [sum_of_fn]⟩,
  obtain ⟨j, rfl⟩ : ∃ (j : fin n), f j = i, by rwa [mem_of_fn, set.mem_range] at hi',
  exact (hi.2 j).1
end

@[simp] lemma comp_change_of_variables_length
  (m M N : ℕ) {i : Σ n, (fin n) → ℕ} (hi : i ∈ comp_partial_sum_source m M N) :
  composition.length (comp_change_of_variables m M N i hi).2 = i.1 :=
begin
  rcases i with ⟨k, blocks_fun⟩,
  dsimp [comp_change_of_variables],
  simp only [composition.length, map_of_fn, length_of_fn]
end

lemma comp_change_of_variables_blocks_fun
  (m M N : ℕ) {i : Σ n, (fin n) → ℕ} (hi : i ∈ comp_partial_sum_source m M N) (j : fin i.1) :
  (comp_change_of_variables m M N i hi).2.blocks_fun
    ⟨j, (comp_change_of_variables_length m M N hi).symm ▸ j.2⟩ = i.2 j :=
begin
  rcases i with ⟨n, f⟩,
  dsimp [composition.blocks_fun, composition.blocks, comp_change_of_variables],
  simp only [map_of_fn, nth_le_of_fn', function.comp_app],
  apply congr_arg,
  exact fin.eta _ _
end

/-- Target set in the change of variables to compute the composition of partial sums of formal
power series, here given a a set. -/
def comp_partial_sum_target_set (m M N : ℕ) : set (Σ n, composition n) :=
{i | (m ≤ i.2.length) ∧ (i.2.length < M) ∧ (∀ (j : fin i.2.length), i.2.blocks_fun j < N)}

lemma comp_partial_sum_target_subset_image_comp_partial_sum_source
  (m M N : ℕ) (i : Σ n, composition n) (hi : i ∈ comp_partial_sum_target_set m M N) :
  ∃ j (hj : j ∈ comp_partial_sum_source m M N), i = comp_change_of_variables m M N j hj :=
begin
  rcases i with ⟨n, c⟩,
  refine ⟨⟨c.length, c.blocks_fun⟩, _, _⟩,
  { simp only [comp_partial_sum_target_set, set.mem_set_of_eq] at hi,
    simp only [mem_comp_partial_sum_source_iff, hi.left, hi.right, true_and, and_true],
    exact λ a, c.one_le_blocks' _ },
  { dsimp [comp_change_of_variables],
    rw composition.sigma_eq_iff_blocks_eq,
    simp only [composition.blocks_fun, composition.blocks, subtype.coe_eta, nth_le_map'],
    conv_lhs { rw ← of_fn_nth_le c.blocks } }
end

/-- Target set in the change of variables to compute the composition of partial sums of formal
power series, here given a a finset.
See also `comp_partial_sum`. -/
def comp_partial_sum_target (m M N : ℕ) : finset (Σ n, composition n) :=
set.finite.to_finset $ ((finset.finite_to_set _).dependent_image _).subset $
  comp_partial_sum_target_subset_image_comp_partial_sum_source m M N

@[simp] lemma mem_comp_partial_sum_target_iff {m M N : ℕ} {a : Σ n, composition n} :
  a ∈ comp_partial_sum_target m M N ↔
    m ≤ a.2.length ∧ a.2.length < M ∧ (∀ (j : fin a.2.length), a.2.blocks_fun j < N) :=
by simp [comp_partial_sum_target, comp_partial_sum_target_set]

/-- `comp_change_of_variables m M N` is a bijection between `comp_partial_sum_source m M N`
and `comp_partial_sum_target m M N`, yielding equal sums for functions that correspond to each
other under the bijection. As `comp_change_of_variables m M N` is a dependent function, stating
that it is a bijection is not directly possible, but the consequence on sums can be stated
more easily. -/
lemma comp_change_of_variables_sum {α : Type*} [add_comm_monoid α] (m M N : ℕ)
  (f : (Σ (n : ℕ), fin n → ℕ) → α) (g : (Σ n, composition n) → α)
  (h : ∀ e (he : e ∈ comp_partial_sum_source m M N),
    f e = g (comp_change_of_variables m M N e he)) :
  ∑ e in comp_partial_sum_source m M N, f e = ∑ e in comp_partial_sum_target m M N, g e :=
begin
  apply finset.sum_bij (comp_change_of_variables m M N),
  -- We should show that the correspondance we have set up is indeed a bijection
  -- between the index sets of the two sums.
  -- 1 - show that the image belongs to `comp_partial_sum_target m N N`
  { rintros ⟨k, blocks_fun⟩ H,
    rw mem_comp_partial_sum_source_iff at H,
    simp only [mem_comp_partial_sum_target_iff, composition.length, composition.blocks, H.left,
               map_of_fn, length_of_fn, true_and, comp_change_of_variables],
    assume j,
    simp only [composition.blocks_fun, (H.right _).right, nth_le_of_fn'] },
  -- 2 - show that the composition gives the `comp_along_composition` application
  { rintros ⟨k, blocks_fun⟩ H,
    rw h },
  -- 3 - show that the map is injective
  { rintros ⟨k, blocks_fun⟩ ⟨k', blocks_fun'⟩ H H' heq,
    obtain rfl : k = k',
    { have := (comp_change_of_variables_length m M N H).symm,
      rwa [heq, comp_change_of_variables_length] at this, },
    congr,
    funext i,
    calc blocks_fun i = (comp_change_of_variables m M N _ H).2.blocks_fun _  :
     (comp_change_of_variables_blocks_fun m M N H i).symm
      ... = (comp_change_of_variables m M N _ H').2.blocks_fun _ :
        begin
          apply composition.blocks_fun_congr; try { rw heq },
          refl
        end
      ... = blocks_fun' i : comp_change_of_variables_blocks_fun m M N H' i },
  -- 4 - show that the map is surjective
  { assume i hi,
    apply comp_partial_sum_target_subset_image_comp_partial_sum_source m M N i,
    simpa [comp_partial_sum_target] using hi }
end

/-- The auxiliary set corresponding to the composition of partial sums asymptotically contains
all possible compositions. -/
lemma comp_partial_sum_target_tendsto_at_top :
  tendsto (λ N, comp_partial_sum_target 0 N N) at_top at_top :=
begin
  apply monotone.tendsto_at_top_finset,
  { assume m n hmn a ha,
    have : ∀ i, i < m → i < n := λ i hi, lt_of_lt_of_le hi hmn,
    tidy },
  { rintros ⟨n, c⟩,
    simp only [mem_comp_partial_sum_target_iff],
    obtain ⟨n, hn⟩ : bdd_above ↑(finset.univ.image (λ (i : fin c.length), c.blocks_fun i)) :=
      finset.bdd_above _,
    refine ⟨max n c.length + 1, bot_le, lt_of_le_of_lt (le_max_right n c.length) (lt_add_one _),
      λ j, lt_of_le_of_lt (le_trans _ (le_max_left _ _)) (lt_add_one _)⟩,
    apply hn,
    simp only [finset.mem_image_of_mem, finset.mem_coe, finset.mem_univ] }
end

/-- Composing the partial sums of two multilinear series coincides with the sum over all
compositions in `comp_partial_sum_target 0 N N`. This is precisely the motivation for the
definition of `comp_partial_sum_target`. -/
lemma comp_partial_sum
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F) (N : ℕ) (z : E) :
  q.partial_sum N (∑ i in finset.Ico 1 N, p i (λ j, z)) =
    ∑ i in comp_partial_sum_target 0 N N, q.comp_along_composition p i.2 (λ j, z) :=
begin
  -- we expand the composition, using the multilinearity of `q` to expand along each coordinate.
  suffices H : ∑ n in finset.range N, ∑ r in fintype.pi_finset (λ (i : fin n), finset.Ico 1 N),
    q n (λ (i : fin n), p (r i) (λ j, z)) =
    ∑ i in comp_partial_sum_target 0 N N, q.comp_along_composition p i.2 (λ j, z),
    by simpa only [formal_multilinear_series.partial_sum,
                   continuous_multilinear_map.map_sum_finset] using H,
  -- rewrite the first sum as a big sum over a sigma type, in the finset
  -- `comp_partial_sum_target 0 N N`
  rw [finset.range_eq_Ico, finset.sum_sigma'],
  -- use `comp_change_of_variables_sum`, saying that this change of variables respects sums
  apply comp_change_of_variables_sum 0 N N,
  rintros ⟨k, blocks_fun⟩ H,
  apply congr _ (comp_change_of_variables_length 0 N N H).symm,
  intros,
  rw ← comp_change_of_variables_blocks_fun 0 N N H,
  refl
end

end formal_multilinear_series

open formal_multilinear_series

/-- If two functions `g` and `f` have power series `q` and `p` respectively at `f x` and `x`, then
`g ∘ f` admits the power series `q.comp p` at `x`. -/
theorem has_fpower_series_at.comp {g : F → G} {f : E → F}
  {q : formal_multilinear_series 𝕜 F G} {p : formal_multilinear_series 𝕜 E F} {x : E}
  (hg : has_fpower_series_at g q (f x)) (hf : has_fpower_series_at f p x) :
  has_fpower_series_at (g ∘ f) (q.comp p) x :=
begin
  /- Consider `rf` and `rg` such that `f` and `g` have power series expansion on the disks
  of radius `rf` and `rg`. -/
  rcases hg with ⟨rg, Hg⟩,
  rcases hf with ⟨rf, Hf⟩,
  /- The terms defining `q.comp p` are geometrically summable in a disk of some radius `r`. -/
  rcases q.comp_summable_nnreal p Hg.radius_pos Hf.radius_pos with ⟨r, r_pos : 0 < r, hr⟩,
  /- We will consider `y` which is smaller than `r` and `rf`, and also small enough that
  `f (x + y)` is close enough to `f x` to be in the disk where `g` is well behaved. Let
  `min (r, rf, δ)` be this new radius.-/
  have : continuous_at f x := Hf.analytic_at.continuous_at,
  obtain ⟨δ, δpos, hδ⟩ : ∃ (δ : ℝ≥0∞) (H : 0 < δ),
    ∀ {z : E}, z ∈ emetric.ball x δ → f z ∈ emetric.ball (f x) rg,
  { have : emetric.ball (f x) rg ∈ 𝓝 (f x) := emetric.ball_mem_nhds _ Hg.r_pos,
    rcases emetric.mem_nhds_iff.1 (Hf.analytic_at.continuous_at this) with ⟨δ, δpos, Hδ⟩,
    exact ⟨δ, δpos, λ z hz, Hδ hz⟩ },
  let rf' := min rf δ,
  have min_pos : 0 < min rf' r,
    by simp only [r_pos, Hf.r_pos, δpos, lt_min_iff, ennreal.coe_pos, and_self],
  /- We will show that `g ∘ f` admits the power series `q.comp p` in the disk of
  radius `min (r, rf', δ)`. -/
  refine ⟨min rf' r, _⟩,
  refine ⟨le_trans (min_le_right rf' r)
    (formal_multilinear_series.le_comp_radius_of_summable q p r hr), min_pos, λ y hy, _⟩,
  /- Let `y` satisfy `∥y∥ < min (r, rf', δ)`. We want to show that `g (f (x + y))` is the sum of
  `q.comp p` applied to `y`. -/
  -- First, check that `y` is small enough so that estimates for `f` and `g` apply.
  have y_mem : y ∈ emetric.ball (0 : E) rf :=
    (emetric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _))) hy,
  have fy_mem : f (x + y) ∈ emetric.ball (f x) rg,
  { apply hδ,
    have : y ∈ emetric.ball (0 : E) δ :=
      (emetric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _))) hy,
    simpa [edist_eq_coe_nnnorm_sub, edist_eq_coe_nnnorm] },
  /- Now the proof starts. To show that the sum of `q.comp p` at `y` is `g (f (x + y))`, we will
  write `q.comp p` applied to `y` as a big sum over all compositions. Since the sum is
  summable, to get its convergence it suffices to get the convergence along some increasing sequence
  of sets. We will use the sequence of sets `comp_partial_sum_target 0 n n`, along which the sum is
  exactly the composition of the partial sums of `q` and `p`, by design. To show that it converges
  to `g (f (x + y))`, pointwise convergence would not be enough, but we have uniform convergence
  to save the day. -/
  -- First step: the partial sum of `p` converges to `f (x + y)`.
  have A : tendsto (λ n, ∑ a in finset.Ico 1 n, p a (λ b, y)) at_top (𝓝 (f (x + y) - f x)),
  { have L : ∀ᶠ n in at_top, ∑ a in finset.range n, p a (λ b, y) - f x =
      ∑ a in finset.Ico 1 n, p a (λ b, y),
    { rw eventually_at_top,
      refine ⟨1, λ n hn, _⟩,
      symmetry,
      rw [eq_sub_iff_add_eq', finset.range_eq_Ico, ← Hf.coeff_zero (λi, y),
          finset.sum_eq_sum_Ico_succ_bot hn] },
    have : tendsto (λ n, ∑ a in finset.range n, p a (λ b, y) - f x) at_top (𝓝 (f (x + y) - f x)) :=
      (Hf.has_sum y_mem).tendsto_sum_nat.sub tendsto_const_nhds,
    exact tendsto.congr' L this },
  -- Second step: the composition of the partial sums of `q` and `p` converges to `g (f (x + y))`.
  have B : tendsto (λ n, q.partial_sum n (∑ a in finset.Ico 1 n, p a (λ b, y)))
    at_top (𝓝 (g (f (x + y)))),
  { -- we use the fact that the partial sums of `q` converge locally uniformly to `g`, and that
    -- composition passes to the limit under locally uniform convergence.
    have B₁ : continuous_at (λ (z : F), g (f x + z)) (f (x + y) - f x),
    { refine continuous_at.comp _ (continuous_const.add continuous_id).continuous_at,
      simp only [add_sub_cancel'_right, id.def],
      exact Hg.continuous_on.continuous_at (is_open.mem_nhds (emetric.is_open_ball) fy_mem) },
    have B₂ : f (x + y) - f x ∈ emetric.ball (0 : F) rg,
      by simpa [edist_eq_coe_nnnorm, edist_eq_coe_nnnorm_sub] using fy_mem,
    rw [← nhds_within_eq_of_open B₂ emetric.is_open_ball] at A,
    convert Hg.tendsto_locally_uniformly_on.tendsto_comp B₁.continuous_within_at B₂ A,
    simp only [add_sub_cancel'_right] },
  -- Third step: the sum over all compositions in `comp_partial_sum_target 0 n n` converges to
  -- `g (f (x + y))`. As this sum is exactly the composition of the partial sum, this is a direct
  -- consequence of the second step
  have C : tendsto (λ n,
    ∑ i in comp_partial_sum_target 0 n n, q.comp_along_composition p i.2 (λ j, y))
    at_top (𝓝 (g (f (x + y)))),
  by simpa [comp_partial_sum] using B,
  -- Fourth step: the sum over all compositions is `g (f (x + y))`. This follows from the
  -- convergence along a subsequence proved in the third step, and the fact that the sum is Cauchy
  -- thanks to the summability properties.
  have D : has_sum (λ i : (Σ n, composition n),
    q.comp_along_composition p i.2 (λ j, y)) (g (f (x + y))),
  { have cau : cauchy_seq (λ (s : finset (Σ n, composition n)),
      ∑ i in s, q.comp_along_composition p i.2 (λ j, y)),
    { apply cauchy_seq_finset_of_norm_bounded _ (nnreal.summable_coe.2 hr) _,
      simp only [coe_nnnorm, nnreal.coe_mul, nnreal.coe_pow],
      rintros ⟨n, c⟩,
      calc ∥(comp_along_composition q p c) (λ (j : fin n), y)∥
      ≤ ∥comp_along_composition q p c∥ * ∏ j : fin n, ∥y∥ :
        by apply continuous_multilinear_map.le_op_norm
      ... ≤ ∥comp_along_composition q p c∥ * (r : ℝ) ^ n :
        begin
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
          rw [finset.prod_const, finset.card_fin],
          apply pow_le_pow_of_le_left (norm_nonneg _),
          rw [emetric.mem_ball, edist_eq_coe_nnnorm] at hy,
          have := (le_trans (le_of_lt hy) (min_le_right _ _)),
          rwa [ennreal.coe_le_coe, ← nnreal.coe_le_coe, coe_nnnorm] at this
        end },
    exact tendsto_nhds_of_cauchy_seq_of_subseq cau
          comp_partial_sum_target_tendsto_at_top C },
  -- Fifth step: the sum over `n` of `q.comp p n` can be expressed as a particular resummation of
  -- the sum over all compositions, by grouping together the compositions of the same
  -- integer `n`. The convergence of the whole sum therefore implies the converence of the sum
  -- of `q.comp p n`
  have E : has_sum (λ n, (q.comp p) n (λ j, y)) (g (f (x + y))),
  { apply D.sigma,
    assume n,
    dsimp [formal_multilinear_series.comp],
    convert has_sum_fintype _,
    simp only [continuous_multilinear_map.sum_apply],
    refl },
  exact E
end

/-- If two functions `g` and `f` are analytic respectively at `f x` and `x`, then `g ∘ f` is
analytic at `x`. -/
theorem analytic_at.comp {g : F → G} {f : E → F} {x : E}
  (hg : analytic_at 𝕜 g (f x)) (hf : analytic_at 𝕜 f x) : analytic_at 𝕜 (g ∘ f) x :=
let ⟨q, hq⟩ := hg, ⟨p, hp⟩ := hf in (hq.comp hp).analytic_at


/-!
### Associativity of the composition of formal multilinear series

In this paragraph, we prove the associativity of the composition of formal power series.
By definition,
```
(r.comp q).comp p n v
= ∑_{i₁ + ... + iₖ = n} (r.comp q)ₖ (p_{i₁} (v₀, ..., v_{i₁ -1}), p_{i₂} (...), ..., p_{iₖ}(...))
= ∑_{a : composition n} (r.comp q) a.length (apply_composition p a v)
```
decomposing `r.comp q` in the same way, we get
```
(r.comp q).comp p n v
= ∑_{a : composition n} ∑_{b : composition a.length}
  r b.length (apply_composition q b (apply_composition p a v))
```
On the other hand,
```
r.comp (q.comp p) n v = ∑_{c : composition n} r c.length (apply_composition (q.comp p) c v)
```
Here, `apply_composition (q.comp p) c v` is a vector of length `c.length`, whose `i`-th term is
given by `(q.comp p) (c.blocks_fun i) (v_l, v_{l+1}, ..., v_{m-1})` where `{l, ..., m-1}` is the
`i`-th block in the composition `c`, of length `c.blocks_fun i` by definition. To compute this term,
we expand it as `∑_{dᵢ : composition (c.blocks_fun i)} q dᵢ.length (apply_composition p dᵢ v')`,
where `v' = (v_l, v_{l+1}, ..., v_{m-1})`. Therefore, we get
```
r.comp (q.comp p) n v =
∑_{c : composition n} ∑_{d₀ : composition (c.blocks_fun 0),
  ..., d_{c.length - 1} : composition (c.blocks_fun (c.length - 1))}
  r c.length (λ i, q dᵢ.length (apply_composition p dᵢ v'ᵢ))
```
To show that these terms coincide, we need to explain how to reindex the sums to put them in
bijection (and then the terms we are summing will correspond to each other). Suppose we have a
composition `a` of `n`, and a composition `b` of `a.length`. Then `b` indicates how to group
together some blocks of `a`, giving altogether `b.length` blocks of blocks. These blocks of blocks
can be called `d₀, ..., d_{a.length - 1}`, and one obtains a composition `c` of `n` by saying that
each `dᵢ` is one single block. Conversely, if one starts from `c` and the `dᵢ`s, one can concatenate
the `dᵢ`s to obtain a composition `a` of `n`, and register the lengths of the `dᵢ`s in a composition
`b` of `a.length`.

An example might be enlightening. Suppose `a = [2, 2, 3, 4, 2]`. It is a composition of
length 5 of 13. The content of the blocks may be represented as `0011222333344`.
Now take `b = [2, 3]` as a composition of `a.length = 5`. It says that the first 2 blocks of `a`
should be merged, and the last 3 blocks of `a` should be merged, giving a new composition of `13`
made of two blocks of length `4` and `9`, i.e., `c = [4, 9]`. But one can also remember that
the new first block was initially made of two blocks of size `2`, so `d₀ = [2, 2]`, and the new
second block was initially made of three blocks of size `3`, `4` and `2`, so `d₁ = [3, 4, 2]`.

This equivalence is called `composition.sigma_equiv_sigma_pi n` below.

We start with preliminary results on compositions, of a very specialized nature, then define the
equivalence `composition.sigma_equiv_sigma_pi n`, and we deduce finally the associativity of
composition of formal multilinear series in `formal_multilinear_series.comp_assoc`.
-/

namespace composition

variable {n : ℕ}

/-- Rewriting equality in the dependent type `Σ (a : composition n), composition a.length)` in
non-dependent terms with lists, requiring that the blocks coincide. -/
lemma sigma_composition_eq_iff (i j : Σ (a : composition n), composition a.length) :
  i = j ↔ i.1.blocks = j.1.blocks ∧ i.2.blocks = j.2.blocks :=
begin
  refine ⟨by rintro rfl; exact ⟨rfl, rfl⟩, _⟩,
  rcases i with ⟨a, b⟩,
  rcases j with ⟨a', b'⟩,
  rintros ⟨h, h'⟩,
  have H : a = a', by { ext1, exact h },
  induction H, congr, ext1, exact h'
end

/-- Rewriting equality in the dependent type
`Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i)` in
non-dependent terms with lists, requiring that the lists of blocks coincide. -/
lemma sigma_pi_composition_eq_iff
  (u v : Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i)) :
  u = v ↔ of_fn (λ i, (u.2 i).blocks) = of_fn (λ i, (v.2 i).blocks) :=
begin
  refine ⟨λ H, by rw H, λ H, _⟩,
  rcases u with ⟨a, b⟩,
  rcases v with ⟨a', b'⟩,
  dsimp at H,
  have h : a = a',
  { ext1,
    have : map list.sum (of_fn (λ (i : fin (composition.length a)), (b i).blocks)) =
      map list.sum (of_fn (λ (i : fin (composition.length a')), (b' i).blocks)), by rw H,
    simp only [map_of_fn] at this,
    change of_fn (λ (i : fin (composition.length a)), (b i).blocks.sum) =
      of_fn (λ (i : fin (composition.length a')), (b' i).blocks.sum) at this,
    simpa [composition.blocks_sum, composition.of_fn_blocks_fun] using this },
  induction h,
  simp only [true_and, eq_self_iff_true, heq_iff_eq],
  ext i : 2,
  have : nth_le (of_fn (λ (i : fin (composition.length a)), (b i).blocks)) i (by simp [i.is_lt]) =
         nth_le (of_fn (λ (i : fin (composition.length a)), (b' i).blocks)) i (by simp [i.is_lt]) :=
    nth_le_of_eq H _,
  rwa [nth_le_of_fn, nth_le_of_fn] at this
end

/-- When `a` is a composition of `n` and `b` is a composition of `a.length`, `a.gather b` is the
composition of `n` obtained by gathering all the blocks of `a` corresponding to a block of `b`.
For instance, if `a = [6, 5, 3, 5, 2]` and `b = [2, 3]`, one should gather together
the first two blocks of `a` and its last three blocks, giving `a.gather b = [11, 10]`. -/
def gather (a : composition n) (b : composition a.length) : composition n :=
{ blocks := (a.blocks.split_wrt_composition b).map sum,
  blocks_pos :=
  begin
    rw forall_mem_map_iff,
    intros j hj,
    suffices H : ∀ i ∈ j, 1 ≤ i, from
      calc 0 < j.length : length_pos_of_mem_split_wrt_composition hj
        ... ≤ j.sum    : length_le_sum_of_one_le _ H,
    intros i hi,
    apply a.one_le_blocks,
    rw ← a.blocks.join_split_wrt_composition b,
    exact mem_join_of_mem hj hi,
  end,
  blocks_sum := by { rw [← sum_join, join_split_wrt_composition, a.blocks_sum] } }

lemma length_gather (a : composition n) (b : composition a.length) :
  length (a.gather b) = b.length :=
show (map list.sum (a.blocks.split_wrt_composition b)).length = b.blocks.length,
by rw [length_map, length_split_wrt_composition]

/-- An auxiliary function used in the definition of `sigma_equiv_sigma_pi` below, associating to
two compositions `a` of `n` and `b` of `a.length`, and an index `i` bounded by the length of
`a.gather b`, the subcomposition of `a` made of those blocks belonging to the `i`-th block of
`a.gather b`. -/
def sigma_composition_aux (a : composition n) (b : composition a.length)
  (i : fin (a.gather b).length) :
  composition ((a.gather b).blocks_fun i) :=
{ blocks := nth_le (a.blocks.split_wrt_composition b) i
    (by { rw [length_split_wrt_composition, ← length_gather], exact i.2 }),
  blocks_pos := assume i hi, a.blocks_pos
    (by { rw ← a.blocks.join_split_wrt_composition b,
          exact mem_join_of_mem (nth_le_mem _ _ _) hi }),
  blocks_sum := by simp only [composition.blocks_fun, nth_le_map', composition.gather] }

lemma length_sigma_composition_aux (a : composition n) (b : composition a.length)
  (i : fin b.length) :
  composition.length (composition.sigma_composition_aux a b ⟨i, (length_gather a b).symm ▸ i.2⟩) =
    composition.blocks_fun b i :=
show list.length (nth_le (split_wrt_composition a.blocks b) i _) = blocks_fun b i,
by { rw [nth_le_map_rev list.length, nth_le_of_eq (map_length_split_wrt_composition _ _)], refl }

lemma blocks_fun_sigma_composition_aux (a : composition n) (b : composition a.length)
  (i : fin b.length) (j : fin (blocks_fun b i)) :
  blocks_fun (sigma_composition_aux a b ⟨i, (length_gather a b).symm ▸ i.2⟩)
      ⟨j, (length_sigma_composition_aux a b i).symm ▸ j.2⟩ = blocks_fun a (embedding b i j) :=
show nth_le (nth_le _ _ _) _ _ = nth_le a.blocks _ _,
by { rw [nth_le_of_eq (nth_le_split_wrt_composition _ _ _), nth_le_drop', nth_le_take'], refl }

/-- Auxiliary lemma to prove that the composition of formal multilinear series is associative.

Consider a composition `a` of `n` and a composition `b` of `a.length`. Grouping together some
blocks of `a` according to `b` as in `a.gather b`, one can compute the total size of the blocks
of `a` up to an index `size_up_to b i + j` (where the `j` corresponds to a set of blocks of `a`
that do not fill a whole block of `a.gather b`). The first part corresponds to a sum of blocks
in `a.gather b`, and the second one to a sum of blocks in the next block of
`sigma_composition_aux a b`. This is the content of this lemma. -/
lemma size_up_to_size_up_to_add (a : composition n) (b : composition a.length)
  {i j : ℕ} (hi : i < b.length) (hj : j < blocks_fun b ⟨i, hi⟩) :
  size_up_to a (size_up_to b i + j) = size_up_to (a.gather b) i +
    (size_up_to (sigma_composition_aux a b ⟨i, (length_gather a b).symm ▸ hi⟩) j) :=
begin
  induction j with j IHj,
  { show sum (take ((b.blocks.take i).sum) a.blocks) =
      sum (take i (map sum (split_wrt_composition a.blocks b))),
    induction i with i IH,
    { refl },
    { have A : i < b.length := nat.lt_of_succ_lt hi,
      have B : i < list.length (map list.sum (split_wrt_composition a.blocks b)), by simp [A],
      have C : 0 < blocks_fun b ⟨i, A⟩ := composition.blocks_pos' _ _ _,
      rw [sum_take_succ _ _ B, ← IH A C],
      have : take (sum (take i b.blocks)) a.blocks =
        take (sum (take i b.blocks)) (take (sum (take (i+1) b.blocks)) a.blocks),
      { rw [take_take, min_eq_left],
        apply monotone_sum_take _ (nat.le_succ _) },
      rw [this, nth_le_map', nth_le_split_wrt_composition,
        ← take_append_drop (sum (take i b.blocks))
          ((take (sum (take (nat.succ i) b.blocks)) a.blocks)), sum_append],
      congr,
      rw [take_append_drop] } },
  { have A : j < blocks_fun b ⟨i, hi⟩ := lt_trans (lt_add_one j) hj,
    have B : j < length (sigma_composition_aux a b ⟨i, (length_gather a b).symm ▸ hi⟩),
      by { convert A, rw [← length_sigma_composition_aux], refl },
    have C : size_up_to b i + j < size_up_to b (i + 1),
    { simp only [size_up_to_succ b hi, add_lt_add_iff_left],
      exact A },
    have D : size_up_to b i + j < length a := lt_of_lt_of_le C (b.size_up_to_le _),
    have : size_up_to b i + nat.succ j = (size_up_to b i + j).succ := rfl,
    rw [this, size_up_to_succ _ D, IHj A, size_up_to_succ _ B],
    simp only [sigma_composition_aux, add_assoc, add_left_inj, fin.coe_mk],
    rw [nth_le_of_eq (nth_le_split_wrt_composition _ _ _), nth_le_drop', nth_le_take _ _ C] }
end

/--
Natural equivalence between `(Σ (a : composition n), composition a.length)` and
`(Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i))`, that shows up as a
change of variables in the proof that composition of formal multilinear series is associative.

Consider a composition `a` of `n` and a composition `b` of `a.length`. Then `b` indicates how to
group together some blocks of `a`, giving altogether `b.length` blocks of blocks. These blocks of
blocks can be called `d₀, ..., d_{a.length - 1}`, and one obtains a composition `c` of `n` by
saying that each `dᵢ` is one single block. The map `⟨a, b⟩ → ⟨c, (d₀, ..., d_{a.length - 1})⟩` is
the direct map in the equiv.

Conversely, if one starts from `c` and the `dᵢ`s, one can join the `dᵢ`s to obtain a composition
`a` of `n`, and register the lengths of the `dᵢ`s in a composition `b` of `a.length`. This is the
inverse map of the equiv.
-/
def sigma_equiv_sigma_pi (n : ℕ) :
  (Σ (a : composition n), composition a.length) ≃
  (Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i)) :=
{ to_fun := λ i, ⟨i.1.gather i.2, i.1.sigma_composition_aux i.2⟩,
  inv_fun := λ i, ⟨
    { blocks := (of_fn (λ j, (i.2 j).blocks)).join,
      blocks_pos :=
      begin
        simp only [and_imp, mem_join, exists_imp_distrib, forall_mem_of_fn_iff],
        exact λ i j hj, composition.blocks_pos _ hj
      end,
      blocks_sum := by simp [sum_of_fn, composition.blocks_sum, composition.sum_blocks_fun] },
    { blocks := of_fn (λ j, (i.2 j).length),
      blocks_pos := forall_mem_of_fn_iff.2
        (λ j, composition.length_pos_of_pos _ (composition.blocks_pos' _ _ _)),
      blocks_sum := by { dsimp only [composition.length], simp [sum_of_fn] } }⟩,
  left_inv :=
  begin
    -- the fact that we have a left inverse is essentially `join_split_wrt_composition`,
    -- but we need to massage it to take care of the dependent setting.
    rintros ⟨a, b⟩,
    rw sigma_composition_eq_iff,
    dsimp,
    split,
    { have A := length_map list.sum (split_wrt_composition a.blocks b),
      conv_rhs { rw [← join_split_wrt_composition a.blocks b,
        ← of_fn_nth_le (split_wrt_composition a.blocks b)] },
      congr,
      { exact A },
      { exact (fin.heq_fun_iff A).2 (λ i, rfl) } },
    { have B : composition.length (composition.gather a b) = list.length b.blocks :=
        composition.length_gather _ _,
      conv_rhs { rw [← of_fn_nth_le b.blocks] },
      congr' 1,
      apply (fin.heq_fun_iff B).2 (λ i, _),
      rw [sigma_composition_aux, composition.length, nth_le_map_rev list.length,
          nth_le_of_eq (map_length_split_wrt_composition _ _)], refl }
  end,
  right_inv :=
  begin
    -- the fact that we have a right inverse is essentially `split_wrt_composition_join`,
    -- but we need to massage it to take care of the dependent setting.
    rintros ⟨c, d⟩,
    have : map list.sum (of_fn (λ (i : fin (composition.length c)), (d i).blocks)) = c.blocks,
      by simp [map_of_fn, (∘), composition.blocks_sum, composition.of_fn_blocks_fun],
    rw sigma_pi_composition_eq_iff,
    dsimp,
    congr,
    { ext1,
      dsimp [composition.gather],
      rwa split_wrt_composition_join,
      simp only [map_of_fn] },
    { rw fin.heq_fun_iff,
      { assume i,
        dsimp [composition.sigma_composition_aux],
        rw [nth_le_of_eq (split_wrt_composition_join _ _ _)],
        { simp only [nth_le_of_fn'] },
        { simp only [map_of_fn] } },
      { congr,
        ext1,
        dsimp [composition.gather],
        rwa split_wrt_composition_join,
        simp only [map_of_fn] } }
  end }

end composition

namespace formal_multilinear_series
open composition

theorem comp_assoc (r : formal_multilinear_series 𝕜 G H) (q : formal_multilinear_series 𝕜 F G)
  (p : formal_multilinear_series 𝕜 E F) :
  (r.comp q).comp p = r.comp (q.comp p) :=
begin
  ext n v,
  /- First, rewrite the two compositions appearing in the theorem as two sums over complicated
  sigma types, as in the description of the proof above. -/
  let f : (Σ (a : composition n), composition a.length) → H :=
    λ c, r c.2.length (apply_composition q c.2 (apply_composition p c.1 v)),
  let g : (Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i)) → H :=
    λ c, r c.1.length (λ (i : fin c.1.length),
      q (c.2 i).length (apply_composition p (c.2 i) (v ∘ c.1.embedding i))),
  suffices : ∑ c, f c = ∑ c, g c,
    by simpa only [formal_multilinear_series.comp, continuous_multilinear_map.sum_apply,
      comp_along_composition_apply, continuous_multilinear_map.map_sum, finset.sum_sigma',
      apply_composition],
  /- Now, we use `composition.sigma_equiv_sigma_pi n` to change
  variables in the second sum, and check that we get exactly the same sums. -/
  rw ← (sigma_equiv_sigma_pi n).sum_comp,
  /- To check that we have the same terms, we should check that we apply the same component of
  `r`, and the same component of `q`, and the same component of `p`, to the same coordinate of
  `v`. This is true by definition, but at each step one needs to convince Lean that the types
  one considers are the same, using a suitable congruence lemma to avoid dependent type issues.
  This dance has to be done three times, one for `r`, one for `q` and one for `p`.-/
  apply finset.sum_congr rfl,
  rintros ⟨a, b⟩ _,
  dsimp [f, g, sigma_equiv_sigma_pi],
  -- check that the `r` components are the same. Based on `composition.length_gather`
  apply r.congr (composition.length_gather a b).symm,
  intros i hi1 hi2,
  -- check that the `q` components are the same. Based on `length_sigma_composition_aux`
  apply q.congr (length_sigma_composition_aux a b _).symm,
  intros j hj1 hj2,
  -- check that the `p` components are the same. Based on `blocks_fun_sigma_composition_aux`
  apply p.congr (blocks_fun_sigma_composition_aux a b _ _).symm,
  intros k hk1 hk2,
  -- finally, check that the coordinates of `v` one is using are the same. Based on
  -- `size_up_to_size_up_to_add`.
  refine congr_arg v (fin.eq_of_veq _),
  dsimp [composition.embedding],
  rw [size_up_to_size_up_to_add _ _ hi1 hj1, add_assoc],
end

end formal_multilinear_series
