/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin
-/
import algebra.big_operators.pi
import algebra.module.pi
import algebra.module.linear_map
import algebra.big_operators.ring
import algebra.star.basic
import data.equiv.ring
import data.fintype.card
import data.matrix.dmatrix

/-!
# Matrices
-/
universes u u' v w

open_locale big_operators
open dmatrix

/-- `matrix m n` is the type of matrices whose rows are indexed by the fintype `m`
    and whose columns are indexed by the fintype `n`. -/
@[nolint unused_arguments]
def matrix (m : Type u) (n : Type u') [fintype m] [fintype n] (α : Type v) : Type (max u u' v) :=
m → n → α

variables {l m n o : Type*} [fintype l] [fintype m] [fintype n] [fintype o]
variables {m' : o → Type*} [∀ i, fintype (m' i)]
variables {n' : o → Type*} [∀ i, fintype (n' i)]
variables {R : Type*} {S : Type*} {α : Type v} {β : Type w}

namespace matrix

section ext
variables {M N : matrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
⟨λ h, funext $ λ i, funext $ h i, λ h, by simp [h]⟩

@[ext] theorem ext : (∀ i j, M i j = N i j) → M = N :=
ext_iff.mp

end ext

/-- `M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`. -/
def map (M : matrix m n α) (f : α → β) : matrix m n β := λ i j, f (M i j)

@[simp]
lemma map_apply {M : matrix m n α} {f : α → β} {i : m} {j : n} :
  M.map f i j = f (M i j) := rfl

@[simp]
lemma map_map {M : matrix m n α} {β γ : Type*} {f : α → β} {g : β → γ} :
  (M.map f).map g = M.map (g ∘ f) :=
by { ext, simp, }

/-- The transpose of a matrix. -/
def transpose (M : matrix m n α) : matrix n m α
| x y := M y x

localized "postfix `ᵀ`:1500 := matrix.transpose" in matrix

/-- `matrix.col u` is the column matrix whose entries are given by `u`. -/
def col (w : m → α) : matrix m unit α
| x y := w x

/-- `matrix.row u` is the row matrix whose entries are given by `u`. -/
def row (v : n → α) : matrix unit n α
| x y := v y

instance [inhabited α] : inhabited (matrix m n α) := pi.inhabited _
instance [has_add α] : has_add (matrix m n α) := pi.has_add
instance [add_semigroup α] : add_semigroup (matrix m n α) := pi.add_semigroup
instance [add_comm_semigroup α] : add_comm_semigroup (matrix m n α) := pi.add_comm_semigroup
instance [has_zero α] : has_zero (matrix m n α) := pi.has_zero
instance [add_monoid α] : add_monoid (matrix m n α) := pi.add_monoid
instance [add_comm_monoid α] : add_comm_monoid (matrix m n α) := pi.add_comm_monoid
instance [has_neg α] : has_neg (matrix m n α) := pi.has_neg
instance [has_sub α] : has_sub (matrix m n α) := pi.has_sub
instance [add_group α] : add_group (matrix m n α) := pi.add_group
instance [add_comm_group α] : add_comm_group (matrix m n α) := pi.add_comm_group
instance [unique α] : unique (matrix m n α) := pi.unique
instance [subsingleton α] : subsingleton (matrix m n α) := pi.subsingleton
instance [nonempty m] [nonempty n] [nontrivial α] : nontrivial (matrix m n α) :=
function.nontrivial

instance [has_scalar R α] : has_scalar R (matrix m n α) := pi.has_scalar
instance [has_scalar R α] [has_scalar S α] [smul_comm_class R S α] :
  smul_comm_class R S (matrix m n α) := pi.smul_comm_class
instance [has_scalar R S] [has_scalar R α] [has_scalar S α] [is_scalar_tower R S α] :
  is_scalar_tower R S (matrix m n α) := pi.is_scalar_tower
instance [monoid R] [mul_action R α] :
  mul_action R (matrix m n α) := pi.mul_action _
instance [monoid R] [add_monoid α] [distrib_mul_action R α] :
  distrib_mul_action R (matrix m n α) := pi.distrib_mul_action _
instance [semiring R] [add_comm_monoid α] [module R α] :
  module R (matrix m n α) := pi.module _ _ _

@[simp] lemma map_zero [has_zero α] [has_zero β] {f : α → β} (h : f 0 = 0) :
  (0 : matrix m n α).map f = 0 :=
by { ext, simp [h], }

lemma map_add [add_monoid α] [add_monoid β] (f : α →+ β)
  (M N : matrix m n α) : (M + N).map f = M.map f + N.map f :=
by { ext, simp, }

lemma map_sub [add_group α] [add_group β] (f : α →+ β)
  (M N : matrix m n α) : (M - N).map f = M.map f - N.map f :=
by { ext, simp }

lemma map_smul [has_scalar R α] [has_scalar R β] (f : α →[R] β) (r : R)
  (M : matrix m n α) : (r • M).map f = r • (M.map f) :=
by { ext, simp, }

-- TODO[gh-6025]: make this an instance once safe to do so
lemma subsingleton_of_empty_left [is_empty m] : subsingleton (matrix m n α) :=
⟨λ M N, by { ext, exact is_empty_elim i }⟩

-- TODO[gh-6025]: make this an instance once safe to do so
lemma subsingleton_of_empty_right [is_empty n] : subsingleton (matrix m n α) :=
⟨λ M N, by { ext, exact is_empty_elim j }⟩

end matrix

/-- The `add_monoid_hom` between spaces of matrices induced by an `add_monoid_hom` between their
coefficients. -/
def add_monoid_hom.map_matrix [add_monoid α] [add_monoid β] (f : α →+ β) :
  matrix m n α →+ matrix m n β :=
{ to_fun := λ M, M.map f,
  map_zero' := by simp,
  map_add' := matrix.map_add f, }

@[simp] lemma add_monoid_hom.map_matrix_apply [add_monoid α] [add_monoid β]
  (f : α →+ β) (M : matrix m n α) : f.map_matrix M = M.map f := rfl

/-- The `linear_map` between spaces of matrices induced by a `linear_map` between their
coefficients. -/
@[simps]
def linear_map.map_matrix [semiring R] [add_comm_monoid α] [add_comm_monoid β]
  [module R α] [module R β] (f : α →ₗ[R] β) : matrix m n α →ₗ[R] matrix m n β :=
{ to_fun := λ M, M.map f,
  map_add' := matrix.map_add f.to_add_monoid_hom,
  map_smul' := matrix.map_smul f.to_mul_action_hom, }

open_locale matrix

namespace matrix

section diagonal
variables [decidable_eq n]

/-- `diagonal d` is the square matrix such that `(diagonal d) i i = d i` and `(diagonal d) i j = 0`
if `i ≠ j`. -/
def diagonal [has_zero α] (d : n → α) : matrix n n α := λ i j, if i = j then d i else 0

@[simp] theorem diagonal_apply_eq [has_zero α] {d : n → α} (i : n) : (diagonal d) i i = d i :=
by simp [diagonal]

@[simp] theorem diagonal_apply_ne [has_zero α] {d : n → α} {i j : n} (h : i ≠ j) :
  (diagonal d) i j = 0 := by simp [diagonal, h]

theorem diagonal_apply_ne' [has_zero α] {d : n → α} {i j : n} (h : j ≠ i) :
  (diagonal d) i j = 0 := diagonal_apply_ne h.symm

@[simp] theorem diagonal_zero [has_zero α] : (diagonal (λ _, 0) : matrix n n α) = 0 :=
by simp [diagonal]; refl

@[simp] lemma diagonal_transpose [has_zero α] (v : n → α) :
  (diagonal v)ᵀ = diagonal v :=
begin
  ext i j,
  by_cases h : i = j,
  { simp [h, transpose] },
  { simp [h, transpose, diagonal_apply_ne' h] }
end

@[simp] theorem diagonal_add [add_monoid α] (d₁ d₂ : n → α) :
  diagonal d₁ + diagonal d₂ = diagonal (λ i, d₁ i + d₂ i) :=
by ext i j; by_cases h : i = j; simp [h]

@[simp] lemma diagonal_map [has_zero α] [has_zero β] {f : α → β} (h : f 0 = 0) {d : n → α} :
  (diagonal d).map f = diagonal (λ m, f (d m)) :=
by { ext, simp only [diagonal, map_apply], split_ifs; simp [h], }

section one
variables [has_zero α] [has_one α]

instance : has_one (matrix n n α) := ⟨diagonal (λ _, 1)⟩

@[simp] theorem diagonal_one : (diagonal (λ _, 1) : matrix n n α) = 1 := rfl

theorem one_apply {i j} : (1 : matrix n n α) i j = if i = j then 1 else 0 := rfl

@[simp] theorem one_apply_eq (i) : (1 : matrix n n α) i i = 1 := diagonal_apply_eq i

@[simp] theorem one_apply_ne {i j} : i ≠ j → (1 : matrix n n α) i j = 0 :=
diagonal_apply_ne

theorem one_apply_ne' {i j} : j ≠ i → (1 : matrix n n α) i j = 0 :=
diagonal_apply_ne'

@[simp] lemma one_map [has_zero β] [has_one β]
  {f : α → β} (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
  (1 : matrix n n α).map f = (1 : matrix n n β) :=
by { ext, simp only [one_apply, map_apply], split_ifs; simp [h₀, h₁], }

end one

section numeral

@[simp] lemma bit0_apply [has_add α] (M : matrix m m α) (i : m) (j : m) :
  (bit0 M) i j = bit0 (M i j) := rfl

variables [add_monoid α] [has_one α]

lemma bit1_apply (M : matrix n n α) (i : n) (j : n) :
  (bit1 M) i j = if i = j then bit1 (M i j) else bit0 (M i j) :=
by dsimp [bit1]; by_cases h : i = j; simp [h]

@[simp]
lemma bit1_apply_eq (M : matrix n n α) (i : n) :
  (bit1 M) i i = bit1 (M i i) :=
by simp [bit1_apply]

@[simp]
lemma bit1_apply_ne (M : matrix n n α) {i j : n} (h : i ≠ j) :
  (bit1 M) i j = bit0 (M i j) :=
by simp [bit1_apply, h]

end numeral

end diagonal

section dot_product

/-- `dot_product v w` is the sum of the entrywise products `v i * w i` -/
def dot_product [has_mul α] [add_comm_monoid α] (v w : m → α) : α :=
∑ i, v i * w i

lemma dot_product_assoc [non_unital_semiring α] (u : m → α) (v : m → n → α) (w : n → α) :
  dot_product (λ j, dot_product u (λ i, v i j)) w = dot_product u (λ i, dot_product (v i) w) :=
by simpa [dot_product, finset.mul_sum, finset.sum_mul, mul_assoc] using finset.sum_comm

lemma dot_product_comm [comm_semiring α] (v w : m → α) :
  dot_product v w = dot_product w v :=
by simp_rw [dot_product, mul_comm]

@[simp] lemma dot_product_punit [add_comm_monoid α] [has_mul α] (v w : punit → α) :
  dot_product v w = v ⟨⟩ * w ⟨⟩ :=
by simp [dot_product]

@[simp] lemma dot_product_zero [non_unital_non_assoc_semiring α] (v : m → α) :
  dot_product v 0 = 0 :=
by simp [dot_product]

@[simp] lemma dot_product_zero' [non_unital_non_assoc_semiring α] (v : m → α) :
  dot_product v (λ _, 0) = 0 :=
dot_product_zero v

@[simp] lemma zero_dot_product [non_unital_non_assoc_semiring α] (v : m → α) :
  dot_product 0 v = 0 :=
by simp [dot_product]

@[simp] lemma zero_dot_product' [non_unital_non_assoc_semiring α] (v : m → α) :
  dot_product (λ _, (0 : α)) v = 0 :=
zero_dot_product v

@[simp] lemma add_dot_product [non_unital_non_assoc_semiring α] (u v w : m → α) :
  dot_product (u + v) w = dot_product u w + dot_product v w :=
by simp [dot_product, add_mul, finset.sum_add_distrib]

@[simp] lemma dot_product_add [non_unital_non_assoc_semiring α] (u v w : m → α) :
  dot_product u (v + w) = dot_product u v + dot_product u w :=
by simp [dot_product, mul_add, finset.sum_add_distrib]

@[simp] lemma diagonal_dot_product [decidable_eq m] [non_unital_non_assoc_semiring α]
  (v w : m → α) (i : m) :
  dot_product (diagonal v i) w = v i * w i :=
have ∀ j ≠ i, diagonal v i j * w j = 0 := λ j hij, by simp [diagonal_apply_ne' hij],
by convert finset.sum_eq_single i (λ j _, this j) _ using 1; simp

@[simp] lemma dot_product_diagonal [decidable_eq m] [non_unital_non_assoc_semiring α]
  (v w : m → α) (i : m) :
  dot_product v (diagonal w i) = v i * w i :=
have ∀ j ≠ i, v j * diagonal w i j = 0 := λ j hij, by simp [diagonal_apply_ne' hij],
by convert finset.sum_eq_single i (λ j _, this j) _ using 1; simp

@[simp] lemma dot_product_diagonal' [decidable_eq m] [non_unital_non_assoc_semiring α]
  (v w : m → α) (i : m) :
  dot_product v (λ j, diagonal w j i) = v i * w i :=
have ∀ j ≠ i, v j * diagonal w j i = 0 := λ j hij, by simp [diagonal_apply_ne hij],
by convert finset.sum_eq_single i (λ j _, this j) _ using 1; simp

@[simp] lemma neg_dot_product [ring α] (v w : m → α) : dot_product (-v) w = - dot_product v w :=
by simp [dot_product]

@[simp] lemma dot_product_neg [ring α] (v w : m → α) : dot_product v (-w) = - dot_product v w :=
by simp [dot_product]

@[simp] lemma smul_dot_product [monoid R] [has_mul α] [add_comm_monoid α] [distrib_mul_action R α]
  [is_scalar_tower R α α] (x : R) (v w : m → α) :
  dot_product (x • v) w = x • dot_product v w :=
by simp [dot_product, finset.smul_sum, smul_mul_assoc]

@[simp] lemma dot_product_smul [monoid R] [has_mul α] [add_comm_monoid α] [distrib_mul_action R α]
  [smul_comm_class R α α] (x : R) (v w : m → α) :
  dot_product v (x • w) = x • dot_product v w :=
by simp [dot_product, finset.smul_sum, mul_smul_comm]

end dot_product

/-- `M ⬝ N` is the usual product of matrices `M` and `N`, i.e. we have that
    `(M ⬝ N) i k` is the dot product of the `i`-th row of `M` by the `k`-th column of `Ǹ`. -/
protected def mul [has_mul α] [add_comm_monoid α] (M : matrix l m α) (N : matrix m n α) :
  matrix l n α :=
λ i k, dot_product (λ j, M i j) (λ j, N j k)

localized "infixl ` ⬝ `:75 := matrix.mul" in matrix

theorem mul_apply [has_mul α] [add_comm_monoid α] {M : matrix l m α} {N : matrix m n α} {i k} :
  (M ⬝ N) i k = ∑ j, M i j * N j k := rfl

instance [has_mul α] [add_comm_monoid α] : has_mul (matrix n n α) := ⟨matrix.mul⟩

@[simp] theorem mul_eq_mul [has_mul α] [add_comm_monoid α] (M N : matrix n n α) :
  M * N = M ⬝ N := rfl

theorem mul_apply' [has_mul α] [add_comm_monoid α] {M N : matrix n n α} {i k} :
  (M ⬝ N) i k = dot_product (λ j, M i j) (λ j, N j k) := rfl

@[simp] theorem diagonal_neg [decidable_eq n] [add_group α] (d : n → α) :
  -diagonal d = diagonal (λ i, -d i) :=
by ext i j; by_cases i = j; simp [h]

lemma sum_apply [add_comm_monoid α] (i : m) (j : n)
  (s : finset β) (g : β → matrix m n α) :
  (∑ c in s, g c) i j = ∑ c in s, g c i j :=
(congr_fun (s.sum_apply i g) j).trans (s.sum_apply j _)

section non_unital_non_assoc_semiring
variables [non_unital_non_assoc_semiring α]

@[simp] protected theorem mul_zero (M : matrix m n α) : M ⬝ (0 : matrix n o α) = 0 :=
by { ext i j, apply dot_product_zero }

@[simp] protected theorem zero_mul (M : matrix m n α) : (0 : matrix l m α) ⬝ M = 0 :=
by { ext i j, apply zero_dot_product }

protected theorem mul_add (L : matrix m n α) (M N : matrix n o α) : L ⬝ (M + N) = L ⬝ M + L ⬝ N :=
by { ext i j, apply dot_product_add }

protected theorem add_mul (L M : matrix l m α) (N : matrix m n α) : (L + M) ⬝ N = L ⬝ N + M ⬝ N :=
by { ext i j, apply add_dot_product }

instance : non_unital_non_assoc_semiring (matrix n n α) :=
{ mul := (*),
  add := (+),
  zero := 0,
  mul_zero := matrix.mul_zero,
  zero_mul := matrix.zero_mul,
  left_distrib := matrix.mul_add,
  right_distrib := matrix.add_mul,
  .. matrix.add_comm_monoid}

@[simp] theorem diagonal_mul [decidable_eq m]
  (d : m → α) (M : matrix m n α) (i j) : (diagonal d).mul M i j = d i * M i j :=
diagonal_dot_product _ _ _

@[simp] theorem mul_diagonal [decidable_eq n]
  (d : n → α) (M : matrix m n α) (i j) : (M ⬝ diagonal d) i j = M i j * d j :=
by { rw ← diagonal_transpose, apply dot_product_diagonal }

@[simp] theorem diagonal_mul_diagonal [decidable_eq n] (d₁ d₂ : n → α) :
  (diagonal d₁) ⬝ (diagonal d₂) = diagonal (λ i, d₁ i * d₂ i) :=
by ext i j; by_cases i = j; simp [h]

theorem diagonal_mul_diagonal' [decidable_eq n] (d₁ d₂ : n → α) :
  diagonal d₁ * diagonal d₂ = diagonal (λ i, d₁ i * d₂ i) :=
diagonal_mul_diagonal _ _

lemma is_add_monoid_hom_mul_left (M : matrix l m α) :
  is_add_monoid_hom (λ x : matrix m n α, M ⬝ x) :=
{ to_is_add_hom := ⟨matrix.mul_add _⟩, map_zero := matrix.mul_zero _ }

lemma is_add_monoid_hom_mul_right (M : matrix m n α) :
  is_add_monoid_hom (λ x : matrix l m α, x ⬝ M) :=
{ to_is_add_hom := ⟨λ _ _, matrix.add_mul _ _ _⟩, map_zero := matrix.zero_mul _ }

protected lemma sum_mul (s : finset β) (f : β → matrix l m α)
  (M : matrix m n α) : (∑ a in s, f a) ⬝ M = ∑ a in s, f a ⬝ M :=
(@finset.sum_hom _ _ _ _ _ s f (λ x, x ⬝ M) M.is_add_monoid_hom_mul_right).symm

protected lemma mul_sum (s : finset β) (f : β → matrix m n α)
  (M : matrix l m α) : M ⬝ ∑ a in s, f a = ∑ a in s, M ⬝ f a :=
(@finset.sum_hom _ _ _ _ _ s f (λ x, M ⬝ x) M.is_add_monoid_hom_mul_left).symm

end non_unital_non_assoc_semiring

section non_assoc_semiring
variables [non_assoc_semiring α]

@[simp] protected theorem one_mul [decidable_eq m] (M : matrix m n α) :
  (1 : matrix m m α) ⬝ M = M :=
by ext i j; rw [← diagonal_one, diagonal_mul, one_mul]

@[simp] protected theorem mul_one [decidable_eq n] (M : matrix m n α) :
  M ⬝ (1 : matrix n n α) = M :=
by ext i j; rw [← diagonal_one, mul_diagonal, mul_one]

instance [decidable_eq n] : non_assoc_semiring (matrix n n α) :=
{ one := 1,
  one_mul := matrix.one_mul,
  mul_one := matrix.mul_one,
  .. matrix.non_unital_non_assoc_semiring }

@[simp]
lemma map_mul {L : matrix m n α} {M : matrix n o α} [non_assoc_semiring β] {f : α →+* β} :
  (L ⬝ M).map f = L.map f ⬝ M.map f :=
by { ext, simp [mul_apply, ring_hom.map_sum], }

end non_assoc_semiring

section non_unital_semiring
variables [non_unital_semiring α]

protected theorem mul_assoc (L : matrix l m α) (M : matrix m n α) (N : matrix n o α) :
  (L ⬝ M) ⬝ N = L ⬝ (M ⬝ N) :=
by { ext, apply dot_product_assoc }

instance : non_unital_semiring (matrix n n α) :=
{ mul_assoc := matrix.mul_assoc, ..matrix.non_unital_non_assoc_semiring }

end non_unital_semiring

section semiring
variables [semiring α]

instance [decidable_eq n] : semiring (matrix n n α) :=
{ ..matrix.non_unital_semiring, ..matrix.non_assoc_semiring }

end semiring

section homs

-- TODO: there should be a way to avoid restating these for each `foo_hom`.
/-- A version of `one_map` where `f` is a ring hom. -/
@[simp] lemma ring_hom_map_one [decidable_eq n] [semiring α] [semiring β] (f : α →+* β) :
  (1 : matrix n n α).map f = 1 :=
one_map f.map_zero f.map_one

/-- A version of `one_map` where `f` is a `ring_equiv`. -/
@[simp] lemma ring_equiv_map_one [decidable_eq n]  [semiring α] [semiring β] (f : α ≃+* β) :
  (1 : matrix n n α).map f = 1 :=
one_map f.map_zero f.map_one

/-- A version of `map_zero` where `f` is a `zero_hom`. -/
@[simp] lemma zero_hom_map_zero [has_zero α] [has_zero β] (f : zero_hom α β) :
  (0 : matrix n n α).map f = 0 :=
map_zero f.map_zero

/-- A version of `map_zero` where `f` is a `add_monoid_hom`. -/
@[simp] lemma add_monoid_hom_map_zero [add_monoid α] [add_monoid β] (f : α →+ β) :
  (0 : matrix n n α).map f = 0 :=
map_zero f.map_zero

/-- A version of `map_zero` where `f` is a `add_equiv`. -/
@[simp] lemma add_equiv_map_zero [add_monoid α] [add_monoid β] (f : α ≃+ β) :
  (0 : matrix n n α).map f = 0 :=
map_zero f.map_zero

/-- A version of `map_zero` where `f` is a `linear_map`. -/
@[simp] lemma linear_map_map_zero [semiring R] [add_comm_monoid α] [add_comm_monoid β]
  [module R α] [module R β] (f : α →ₗ[R] β) :
  (0 : matrix n n α).map f = 0 :=
map_zero f.map_zero

/-- A version of `map_zero` where `f` is a `linear_equiv`. -/
@[simp] lemma linear_equiv_map_zero [semiring R] [add_comm_monoid α] [add_comm_monoid β]
  [module R α] [module R β] (f : α ≃ₗ[R] β) :
  (0 : matrix n n α).map f = 0 :=
map_zero f.map_zero

/-- A version of `map_zero` where `f` is a `ring_hom`. -/
@[simp] lemma ring_hom_map_zero [semiring α] [semiring β] (f : α →+* β) :
  (0 : matrix n n α).map f = 0 :=
map_zero f.map_zero

/-- A version of `map_zero` where `f` is a `ring_equiv`. -/
@[simp] lemma ring_equiv_map_zero [semiring α] [semiring β] (f : α ≃+* β) :
  (0 : matrix n n α).map f = 0 :=
map_zero f.map_zero

end homs

end matrix

/-- The `ring_hom` between spaces of square matrices induced by a `ring_hom` between their
coefficients. -/
@[simps]
def ring_hom.map_matrix [decidable_eq m] [semiring α] [semiring β] (f : α →+* β) :
  matrix m m α →+* matrix m m β :=
{ to_fun := λ M, M.map f,
  map_one' := by simp,
  map_mul' := λ L M, matrix.map_mul,
  ..(f.to_add_monoid_hom).map_matrix }

open_locale matrix

namespace matrix

section ring
variables [ring α]

@[simp] theorem neg_mul (M : matrix m n α) (N : matrix n o α) :
  (-M) ⬝ N = -(M ⬝ N) :=
by { ext, apply neg_dot_product }

@[simp] theorem mul_neg (M : matrix m n α) (N : matrix n o α) :
  M ⬝ (-N) = -(M ⬝ N) :=
by { ext, apply dot_product_neg }

protected theorem sub_mul (M M' : matrix m n α) (N : matrix n o α) :
  (M - M') ⬝ N = M ⬝ N - M' ⬝ N :=
by rw [sub_eq_add_neg, matrix.add_mul, neg_mul, sub_eq_add_neg]

protected theorem mul_sub (M : matrix m n α) (N N' : matrix n o α) :
  M ⬝ (N - N') = M ⬝ N - M ⬝ N' :=
by rw [sub_eq_add_neg, matrix.mul_add, mul_neg, sub_eq_add_neg]

end ring

instance [decidable_eq n] [ring α] : ring (matrix n n α) :=
{ ..matrix.semiring, ..matrix.add_comm_group }

section semiring
variables [semiring α]

lemma smul_eq_diagonal_mul [decidable_eq m] (M : matrix m n α) (a : α) :
  a • M = diagonal (λ _, a) ⬝ M :=
by { ext, simp }

@[simp] lemma smul_mul [monoid R] [distrib_mul_action R α] [is_scalar_tower R α α]
  (a : R) (M : matrix m n α) (N : matrix n l α) :
  (a • M) ⬝ N = a • M ⬝ N :=
by { ext, apply smul_dot_product }

/-- This instance enables use with `smul_mul_assoc`. -/
instance semiring.is_scalar_tower [monoid R] [distrib_mul_action R α] [is_scalar_tower R α α] :
  is_scalar_tower R (matrix n n α) (matrix n n α) :=
⟨λ r m n, matrix.smul_mul r m n⟩

@[simp] lemma mul_smul [monoid R] [distrib_mul_action R α] [smul_comm_class R α α]
  (M : matrix m n α) (a : R) (N : matrix n l α) : M ⬝ (a • N) = a • M ⬝ N :=
by { ext, apply dot_product_smul }

/-- This instance enables use with `mul_smul_comm`. -/
instance semiring.smul_comm_class [monoid R] [distrib_mul_action R α] [smul_comm_class R α α] :
  smul_comm_class R (matrix n n α) (matrix n n α) :=
⟨λ r m n, (matrix.mul_smul m r n).symm⟩

@[simp] lemma mul_mul_left (M : matrix m n α) (N : matrix n o α) (a : α) :
  (λ i j, a * M i j) ⬝ N = a • (M ⬝ N) :=
smul_mul a M N

/--
The ring homomorphism `α →+* matrix n n α`
sending `a` to the diagonal matrix with `a` on the diagonal.
-/
def scalar (n : Type u) [decidable_eq n] [fintype n] : α →+* matrix n n α :=
{ to_fun := λ a, a • 1,
  map_one' := by simp,
  map_mul' := by { intros, ext, simp [mul_assoc], },
  .. (smul_add_hom α _).flip (1 : matrix n n α) }

section scalar

variable [decidable_eq n]

@[simp] lemma coe_scalar : (scalar n : α → matrix n n α) = λ a, a • 1 := rfl

lemma scalar_apply_eq (a : α) (i : n) :
  scalar n a i i = a :=
by simp only [coe_scalar, smul_eq_mul, mul_one, one_apply_eq, pi.smul_apply]

lemma scalar_apply_ne (a : α) (i j : n) (h : i ≠ j) :
  scalar n a i j = 0 :=
by simp only [h, coe_scalar, one_apply_ne, ne.def, not_false_iff, pi.smul_apply, smul_zero]

lemma scalar_inj [nonempty n] {r s : α} : scalar n r = scalar n s ↔ r = s :=
begin
  split,
  { intro h,
    inhabit n,
    rw [← scalar_apply_eq r (arbitrary n), ← scalar_apply_eq s (arbitrary n), h] },
  { rintro rfl, refl }
end

end scalar

end semiring

section comm_semiring
variables [comm_semiring α]

lemma smul_eq_mul_diagonal [decidable_eq n] (M : matrix m n α) (a : α) :
  a • M = M ⬝ diagonal (λ _, a) :=
by { ext, simp [mul_comm] }

@[simp] lemma mul_mul_right (M : matrix m n α) (N : matrix n o α) (a : α) :
  M ⬝ (λ i j, a * N i j) = a • (M ⬝ N) :=
mul_smul M a N

lemma scalar.commute [decidable_eq n] (r : α) (M : matrix n n α) : commute (scalar n r) M :=
by simp [commute, semiconj_by]

end comm_semiring

/-- For two vectors `w` and `v`, `vec_mul_vec w v i j` is defined to be `w i * v j`.
    Put another way, `vec_mul_vec w v` is exactly `col w ⬝ row v`. -/
def vec_mul_vec [has_mul α] (w : m → α) (v : n → α) : matrix m n α
| x y := w x * v y

section non_unital_non_assoc_semiring
variables [non_unital_non_assoc_semiring α]

/-- `mul_vec M v` is the matrix-vector product of `M` and `v`, where `v` is seen as a column matrix.
    Put another way, `mul_vec M v` is the vector whose entries
    are those of `M ⬝ col v` (see `col_mul_vec`). -/
def mul_vec (M : matrix m n α) (v : n → α) : m → α
| i := dot_product (λ j, M i j) v

/-- `vec_mul v M` is the vector-matrix product of `v` and `M`, where `v` is seen as a row matrix.
    Put another way, `vec_mul v M` is the vector whose entries
    are those of `row v ⬝ M` (see `row_vec_mul`). -/
def vec_mul (v : m → α) (M : matrix m n α) : n → α
| j := dot_product v (λ i, M i j)

instance mul_vec.is_add_monoid_hom_left (v : n → α) :
  is_add_monoid_hom (λM:matrix m n α, mul_vec M v) :=
{ map_zero := by ext; simp [mul_vec]; refl,
  map_add :=
  begin
    intros x y,
    ext m,
    apply add_dot_product
  end }

lemma mul_vec_diagonal [decidable_eq m] (v w : m → α) (x : m) :
  mul_vec (diagonal v) w x = v x * w x :=
diagonal_dot_product v w x

lemma vec_mul_diagonal [decidable_eq m] (v w : m → α) (x : m) :
  vec_mul v (diagonal w) x = v x * w x :=
dot_product_diagonal' v w x

@[simp] lemma mul_vec_zero (A : matrix m n α) : mul_vec A 0 = 0 :=
by { ext, simp [mul_vec] }

@[simp] lemma vec_mul_zero (A : matrix m n α) : vec_mul 0 A = 0 :=
by { ext, simp [vec_mul] }

lemma vec_mul_vec_eq (w : m → α) (v : n → α) :
  vec_mul_vec w v = (col w) ⬝ (row v) :=
by { ext i j, simp [vec_mul_vec, mul_apply], refl }

lemma smul_mul_vec_assoc [monoid R] [distrib_mul_action R α] [is_scalar_tower R α α]
  (a : R) (A : matrix m n α) (b : n → α) :
  (a • A).mul_vec b = a • (A.mul_vec b) :=
by { ext, apply smul_dot_product, }

lemma mul_vec_add (A : matrix m n α) (x y : n → α) :
  A.mul_vec (x + y) = A.mul_vec x + A.mul_vec y :=
by { ext, apply dot_product_add }

lemma add_mul_vec (A B : matrix m n α) (x : n → α) :
  (A + B).mul_vec x = A.mul_vec x + B.mul_vec x :=
by { ext, apply add_dot_product }

lemma vec_mul_add (A B : matrix m n α) (x : m → α) :
  vec_mul x (A + B) = vec_mul x A + vec_mul x B :=
by { ext, apply dot_product_add }

lemma add_vec_mul (A : matrix m n α) (x y : m → α) :
  vec_mul (x + y) A = vec_mul x A + vec_mul y A :=
by { ext, apply add_dot_product }

end non_unital_non_assoc_semiring

section non_unital_semiring
variables [non_unital_semiring α]

@[simp] lemma vec_mul_vec_mul (v : m → α) (M : matrix m n α) (N : matrix n o α) :
  vec_mul (vec_mul v M) N = vec_mul v (M ⬝ N) :=
by { ext, apply dot_product_assoc }

@[simp] lemma mul_vec_mul_vec (v : o → α) (M : matrix m n α) (N : matrix n o α) :
  mul_vec M (mul_vec N v) = mul_vec (M ⬝ N) v :=
by { ext, symmetry, apply dot_product_assoc }

end non_unital_semiring

section non_assoc_semiring
variables [non_assoc_semiring α]

@[simp] lemma mul_vec_one [decidable_eq m] (v : m → α) : mul_vec 1 v = v :=
by { ext, rw [←diagonal_one, mul_vec_diagonal, one_mul] }

@[simp] lemma vec_mul_one [decidable_eq m] (v : m → α) : vec_mul v 1 = v :=
by { ext, rw [←diagonal_one, vec_mul_diagonal, mul_one] }

end non_assoc_semiring

section semiring
variables [semiring α]

variables [decidable_eq m] [decidable_eq n]

/--
`std_basis_matrix i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def std_basis_matrix (i : m) (j : n) (a : α) : matrix m n α :=
(λ i' j', if i' = i ∧ j' = j then a else 0)

@[simp] lemma smul_std_basis_matrix (i : m) (j : n) (a b : α) :
b • std_basis_matrix i j a = std_basis_matrix i j (b • a) :=
by { unfold std_basis_matrix, ext, simp }

@[simp] lemma std_basis_matrix_zero (i : m) (j : n) :
std_basis_matrix i j (0 : α) = 0 :=
by { unfold std_basis_matrix, ext, simp }

lemma std_basis_matrix_add (i : m) (j : n) (a b : α) :
std_basis_matrix i j (a + b) = std_basis_matrix i j a + std_basis_matrix i j b :=
begin
  unfold std_basis_matrix, ext,
  split_ifs with h; simp [h],
end

lemma matrix_eq_sum_std_basis (x : matrix n m α) :
  x = ∑ (i : n) (j : m), std_basis_matrix i j (x i j) :=
begin
  ext, symmetry,
  iterate 2 { rw finset.sum_apply },
  convert fintype.sum_eq_single i _,
  { simp [std_basis_matrix] },
  { intros j hj,
    simp [std_basis_matrix, hj.symm] }
end

-- TODO: tie this up with the `basis` machinery of linear algebra
-- this is not completely trivial because we are indexing by two types, instead of one

-- TODO: add `std_basis_vec`
lemma std_basis_eq_basis_mul_basis (i : m) (j : n) :
std_basis_matrix i j 1 = vec_mul_vec (λ i', ite (i = i') 1 0) (λ j', ite (j = j') 1 0) :=
begin
  ext, norm_num [std_basis_matrix, vec_mul_vec],
  split_ifs; tauto,
end

@[elab_as_eliminator] protected lemma induction_on'
  {X : Type*} [semiring X] {M : matrix n n X → Prop} (m : matrix n n X)
  (h_zero : M 0)
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_std_basis : ∀ i j x, M (std_basis_matrix i j x)) :
  M m :=
begin
  rw [matrix_eq_sum_std_basis m, ← finset.sum_product'],
  apply finset.sum_induction _ _ h_add h_zero,
  { intros, apply h_std_basis, }
end

@[elab_as_eliminator] protected lemma induction_on
  [nonempty n] {X : Type*} [semiring X] {M : matrix n n X → Prop} (m : matrix n n X)
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_std_basis : ∀ i j x, M (std_basis_matrix i j x)) :
  M m :=
matrix.induction_on' m
begin
  have i : n := classical.choice (by assumption),
  simpa using h_std_basis i i 0,
end
h_add h_std_basis

end semiring

section ring

variables [ring α]

lemma neg_vec_mul (v : m → α) (A : matrix m n α) : vec_mul (-v) A = - vec_mul v A :=
by { ext, apply neg_dot_product }

lemma vec_mul_neg (v : m → α) (A : matrix m n α) : vec_mul v (-A) = - vec_mul v A :=
by { ext, apply dot_product_neg }

lemma neg_mul_vec (v : n → α) (A : matrix m n α) : mul_vec (-A) v = - mul_vec A v :=
by { ext, apply neg_dot_product }

lemma mul_vec_neg (v : n → α) (A : matrix m n α) : mul_vec A (-v) = - mul_vec A v :=
by { ext, apply dot_product_neg }

end ring

section comm_semiring

variables [comm_semiring α]

lemma mul_vec_smul_assoc (A : matrix m n α) (b : n → α) (a : α) :
  A.mul_vec (a • b) = a • (A.mul_vec b) :=
by { ext, apply dot_product_smul }

lemma mul_vec_transpose (A : matrix m n α) (x : m → α) :
  mul_vec Aᵀ x = vec_mul x A :=
by { ext, apply dot_product_comm }

lemma vec_mul_transpose (A : matrix m n α) (x : n → α) :
  vec_mul x Aᵀ = mul_vec A x :=
by { ext, apply dot_product_comm }

end comm_semiring

section transpose

open_locale matrix

/--
  Tell `simp` what the entries are in a transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
@[simp] lemma transpose_apply (M : matrix m n α) (i j) : M.transpose j i = M i j := rfl

@[simp] lemma transpose_transpose (M : matrix m n α) :
  Mᵀᵀ = M :=
by ext; refl

@[simp] lemma transpose_zero [has_zero α] : (0 : matrix m n α)ᵀ = 0 :=
by ext i j; refl

@[simp] lemma transpose_one [decidable_eq n] [has_zero α] [has_one α] : (1 : matrix n n α)ᵀ = 1 :=
begin
  ext i j,
  unfold has_one.one transpose,
  by_cases i = j,
  { simp only [h, diagonal_apply_eq] },
  { simp only [diagonal_apply_ne h, diagonal_apply_ne (λ p, h (symm p))] }
end

@[simp] lemma transpose_add [has_add α] (M : matrix m n α) (N : matrix m n α) :
  (M + N)ᵀ = Mᵀ + Nᵀ  :=
by { ext i j, simp }

@[simp] lemma transpose_sub [add_group α] (M : matrix m n α) (N : matrix m n α) :
  (M - N)ᵀ = Mᵀ - Nᵀ  :=
by { ext i j, simp }

@[simp] lemma transpose_mul [comm_semiring α] (M : matrix m n α) (N : matrix n l α) :
  (M ⬝ N)ᵀ = Nᵀ ⬝ Mᵀ  :=
begin
  ext i j,
  apply dot_product_comm
end

@[simp] lemma transpose_smul [semiring α] (c : α) (M : matrix m n α) :
  (c • M)ᵀ = c • Mᵀ :=
by { ext i j, refl }

@[simp] lemma transpose_neg [has_neg α] (M : matrix m n α) :
  (- M)ᵀ = - Mᵀ  :=
by ext i j; refl

lemma transpose_map {f : α → β} {M : matrix m n α} : Mᵀ.map f = (M.map f)ᵀ :=
by { ext, refl }

end transpose

section star_ring
variables [decidable_eq n] [semiring α] [star_ring α]

/--
When `R` is a `*`-(semi)ring, `matrix n n R` becomes a `*`-(semi)ring with
the star operation given by taking the conjugate, and the star of each entry.
-/
instance : star_ring (matrix n n α) :=
{ star := λ M, M.transpose.map star,
  star_involutive := λ M, by { ext, simp, },
  star_add := λ M N, by { ext, simp, },
  star_mul := λ M N, by { ext, simp [mul_apply], }, }

@[simp] lemma star_apply (M : matrix n n α) (i j) : star M i j = star (M j i) := rfl

lemma star_mul (M N : matrix n n α) : star (M ⬝ N) = star N ⬝ star M := star_mul _ _

end star_ring

/-- Given maps `(r_reindex : l → m)` and  `(c_reindex : o → n)` reindexing the rows and columns of
a matrix `M : matrix m n α`, the matrix `M.minor r_reindex c_reindex : matrix l o α` is defined
by `(M.minor r_reindex c_reindex) i j = M (r_reindex i) (c_reindex j)` for `(i,j) : l × o`.
Note that the total number of row and columns does not have to be preserved. -/
def minor (A : matrix m n α) (r_reindex : l → m) (c_reindex : o → n) : matrix l o α :=
λ i j, A (r_reindex i) (c_reindex j)

@[simp] lemma minor_apply (A : matrix m n α) (r_reindex : l → m) (c_reindex : o → n) (i j) :
  A.minor r_reindex c_reindex i j = A (r_reindex i) (c_reindex j) := rfl

@[simp] lemma minor_id_id (A : matrix m n α) :
  A.minor id id = A :=
ext $ λ _ _, rfl

@[simp] lemma minor_minor {l₂ o₂ : Type*} [fintype l₂] [fintype o₂] (A : matrix m n α)
  (r₁ : l → m) (c₁ : o → n) (r₂ : l₂ → l) (c₂ : o₂ → o) :
  (A.minor r₁ c₁).minor r₂ c₂ = A.minor (r₁ ∘ r₂) (c₁ ∘ c₂) :=
ext $ λ _ _, rfl

@[simp] lemma transpose_minor (A : matrix m n α) (r_reindex : l → m) (c_reindex : o → n) :
  (A.minor r_reindex c_reindex)ᵀ = Aᵀ.minor c_reindex r_reindex :=
ext $ λ _ _, rfl

lemma minor_add [has_add α] (A B : matrix m n α) :
  ((A + B).minor : (l → m) → (o → n) → matrix l o α) = A.minor + B.minor := rfl

lemma minor_neg [has_neg α] (A : matrix m n α) :
  ((-A).minor : (l → m) → (o → n) → matrix l o α) = -A.minor := rfl

lemma minor_sub [has_sub α] (A B : matrix m n α) :
  ((A - B).minor : (l → m) → (o → n) → matrix l o α) = A.minor - B.minor := rfl

@[simp]
lemma minor_zero [has_zero α] :
  ((0 : matrix m n α).minor : (l → m) → (o → n) → matrix l o α) = 0 := rfl

lemma minor_smul {R : Type*} [semiring R] [add_comm_monoid α] [module R α] (r : R)
  (A : matrix m n α) :
  ((r • A : matrix m n α).minor : (l → m) → (o → n) → matrix l o α) = r • A.minor := rfl

lemma minor_map (f : α → β) (e₁ : l → m) (e₂ : o → n) (A : matrix m n α) :
  (A.map f).minor e₁ e₂ = (A.minor e₁ e₂).map f := rfl

/-- Given a `(m × m)` diagonal matrix defined by a map `d : m → α`, if the reindexing map `e` is
  injective, then the resulting matrix is again diagonal. -/
lemma minor_diagonal [has_zero α] [decidable_eq m] [decidable_eq l] (d : m → α) (e : l → m)
  (he : function.injective e) :
  (diagonal d).minor e e = diagonal (d ∘ e) :=
ext $ λ i j, begin
  rw minor_apply,
  by_cases h : i = j,
  { rw [h, diagonal_apply_eq, diagonal_apply_eq], },
  { rw [diagonal_apply_ne h, diagonal_apply_ne (he.ne h)], },
end

lemma minor_one [has_zero α] [has_one α] [decidable_eq m] [decidable_eq l] (e : l → m)
  (he : function.injective e) :
  (1 : matrix m m α).minor e e = 1 :=
minor_diagonal _ e he

lemma minor_mul [semiring α] {p q : Type*} [fintype p] [fintype q]
  (M : matrix m n α) (N : matrix n p α)
  (e₁ : l → m) (e₂ : o → n) (e₃ : q → p) (he₂ : function.bijective e₂) :
  (M ⬝ N).minor e₁ e₃ = (M.minor e₁ e₂) ⬝ (N.minor e₂ e₃) :=
ext $ λ _ _, (he₂.sum_comp _).symm


/-! `simp` lemmas for `matrix.minor`s interaction with `matrix.diagonal`, `1`, and `matrix.mul` for
when the mappings are bundled. -/

@[simp]
lemma minor_diagonal_embedding [has_zero α] [decidable_eq m] [decidable_eq l] (d : m → α)
  (e : l ↪ m) :
  (diagonal d).minor e e = diagonal (d ∘ e) :=
minor_diagonal d e e.injective

@[simp]
lemma minor_diagonal_equiv [has_zero α] [decidable_eq m] [decidable_eq l] (d : m → α)
  (e : l ≃ m) :
  (diagonal d).minor e e = diagonal (d ∘ e) :=
minor_diagonal d e e.injective

@[simp]
lemma minor_one_embedding [has_zero α] [has_one α] [decidable_eq m] [decidable_eq l] (e : l ↪ m) :
  (1 : matrix m m α).minor e e = 1 :=
minor_one e e.injective

@[simp]
lemma minor_one_equiv [has_zero α] [has_one α] [decidable_eq m] [decidable_eq l] (e : l ≃ m) :
  (1 : matrix m m α).minor e e = 1 :=
minor_one e e.injective

lemma minor_mul_equiv [semiring α] {p q : Type*} [fintype p] [fintype q]
  (M : matrix m n α) (N : matrix n p α) (e₁ : l → m) (e₂ : o ≃ n) (e₃ : q → p)  :
  (M ⬝ N).minor e₁ e₃ = (M.minor e₁ e₂) ⬝ (N.minor e₂ e₃) :=
minor_mul M N e₁ e₂ e₃ e₂.bijective

lemma mul_minor_one [semiring α] [decidable_eq o] (e₁ : n ≃ o) (e₂ : l → o) (M : matrix m n α) :
  M ⬝ (1 : matrix o o α).minor e₁ e₂ = minor M id (e₁.symm ∘ e₂) :=
begin
  let A := M.minor id e₁.symm,
  have : M = A.minor id e₁,
  { simp only [minor_minor, function.comp.right_id, minor_id_id, equiv.symm_comp_self], },
  rw [this, ←minor_mul_equiv],
  simp only [matrix.mul_one, minor_minor, function.comp.right_id, minor_id_id,
    equiv.symm_comp_self],
end

lemma one_minor_mul [semiring α] [decidable_eq o] (e₁ : l → o) (e₂ : m ≃ o) (M : matrix m n α) :
  ((1 : matrix o o α).minor e₁ e₂).mul M = minor M (e₂.symm ∘ e₁) id :=
begin
  let A := M.minor e₂.symm id,
  have : M = A.minor e₂ id,
  { simp only [minor_minor, function.comp.right_id, minor_id_id, equiv.symm_comp_self], },
  rw [this, ←minor_mul_equiv],
  simp only [matrix.one_mul, minor_minor, function.comp.right_id, minor_id_id,
    equiv.symm_comp_self],
end

/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
def reindex (eₘ : m ≃ l) (eₙ : n ≃ o) : matrix m n α ≃ matrix l o α :=
{ to_fun    := λ M, M.minor eₘ.symm eₙ.symm,
  inv_fun   := λ M, M.minor eₘ eₙ,
  left_inv  := λ M, by simp,
  right_inv := λ M, by simp, }

@[simp] lemma reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : matrix m n α) :
  reindex eₘ eₙ M = M.minor eₘ.symm eₙ.symm :=
rfl

@[simp] lemma reindex_refl_refl (A : matrix m n α) :
  reindex (equiv.refl _) (equiv.refl _) A = A :=
A.minor_id_id

@[simp] lemma reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
  (reindex eₘ eₙ).symm = (reindex eₘ.symm eₙ.symm : matrix l o α ≃ _) :=
rfl

@[simp] lemma reindex_trans {l₂ o₂ : Type*} [fintype l₂] [fintype o₂]
  (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂) :
  (reindex eₘ eₙ).trans (reindex eₘ₂ eₙ₂) =
    (reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) : matrix m n α ≃ _) :=
equiv.ext $ λ A, (A.minor_minor eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm : _)

lemma transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : matrix m n α) :
  (reindex eₘ eₙ M)ᵀ = (reindex eₙ eₘ Mᵀ) :=
rfl

/-- The left `n × l` part of a `n × (l+r)` matrix. -/
@[reducible]
def sub_left {m l r : nat} (A : matrix (fin m) (fin (l + r)) α) : matrix (fin m) (fin l) α :=
minor A id (fin.cast_add r)

/-- The right `n × r` part of a `n × (l+r)` matrix. -/
@[reducible]
def sub_right {m l r : nat} (A : matrix (fin m) (fin (l + r)) α) : matrix (fin m) (fin r) α :=
minor A id (fin.nat_add l)

/-- The top `u × n` part of a `(u+d) × n` matrix. -/
@[reducible]
def sub_up {d u n : nat} (A : matrix (fin (u + d)) (fin n) α) : matrix (fin u) (fin n) α :=
minor A (fin.cast_add d) id

/-- The bottom `d × n` part of a `(u+d) × n` matrix. -/
@[reducible]
def sub_down {d u n : nat} (A : matrix (fin (u + d)) (fin n) α) : matrix (fin d) (fin n) α :=
minor A (fin.nat_add u) id

/-- The top-right `u × r` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def sub_up_right {d u l r : nat} (A: matrix (fin (u + d)) (fin (l + r)) α) :
  matrix (fin u) (fin r) α :=
sub_up (sub_right A)

/-- The bottom-right `d × r` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def sub_down_right {d u l r : nat} (A : matrix (fin (u + d)) (fin (l + r)) α) :
  matrix (fin d) (fin r) α :=
sub_down (sub_right A)

/-- The top-left `u × l` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def sub_up_left {d u l r : nat} (A : matrix (fin (u + d)) (fin (l + r)) α) :
  matrix (fin u) (fin (l)) α :=
sub_up (sub_left A)

/-- The bottom-left `d × l` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def sub_down_left {d u l r : nat} (A: matrix (fin (u + d)) (fin (l + r)) α) :
  matrix (fin d) (fin (l)) α :=
sub_down (sub_left A)

section row_col
/-!
### `row_col` section

Simplification lemmas for `matrix.row` and `matrix.col`.
-/
open_locale matrix

@[simp] lemma col_add [has_add α] (v w : m → α) : col (v + w) = col v + col w := by { ext, refl }
@[simp] lemma col_smul [has_scalar R α] (x : R) (v : m → α) : col (x • v) = x • col v :=
by { ext, refl }
@[simp] lemma row_add [has_add α] (v w : m → α) : row (v + w) = row v + row w := by { ext, refl }
@[simp] lemma row_smul [has_scalar R α] (x : R) (v : m → α) : row (x • v) = x • row v :=
by { ext, refl }

@[simp] lemma col_apply (v : m → α) (i j) : matrix.col v i j = v i := rfl
@[simp] lemma row_apply (v : m → α) (i j) : matrix.row v i j = v j := rfl

@[simp]
lemma transpose_col (v : m → α) : (matrix.col v).transpose = matrix.row v := by {ext, refl}
@[simp]
lemma transpose_row (v : m → α) : (matrix.row v).transpose = matrix.col v := by {ext, refl}

lemma row_vec_mul [semiring α] (M : matrix m n α) (v : m → α) :
  matrix.row (matrix.vec_mul v M) = matrix.row v ⬝ M := by {ext, refl}
lemma col_vec_mul [semiring α] (M : matrix m n α) (v : m → α) :
  matrix.col (matrix.vec_mul v M) = (matrix.row v ⬝ M)ᵀ := by {ext, refl}
lemma col_mul_vec [semiring α] (M : matrix m n α) (v : n → α) :
  matrix.col (matrix.mul_vec M v) = M ⬝ matrix.col v := by {ext, refl}
lemma row_mul_vec [semiring α] (M : matrix m n α) (v : n → α) :
  matrix.row (matrix.mul_vec M v) = (M ⬝ matrix.col v)ᵀ := by {ext, refl}

@[simp]
lemma row_mul_col_apply [has_mul α] [add_comm_monoid α] (v w : m → α) (i j) :
  (row v ⬝ col w) i j = dot_product v w :=
rfl

end row_col

section update

/-- Update, i.e. replace the `i`th row of matrix `A` with the values in `b`. -/
def update_row [decidable_eq n] (M : matrix n m α) (i : n) (b : m → α) : matrix n m α :=
function.update M i b

/-- Update, i.e. replace the `j`th column of matrix `A` with the values in `b`. -/
def update_column [decidable_eq m] (M : matrix n m α) (j : m) (b : n → α) : matrix n m α :=
λ i, function.update (M i) j (b i)

variables {M : matrix n m α} {i : n} {j : m} {b : m → α} {c : n → α}

@[simp] lemma update_row_self [decidable_eq n] : update_row M i b i = b :=
function.update_same i b M

@[simp] lemma update_column_self [decidable_eq m] : update_column M j c i j = c i :=
function.update_same j (c i) (M i)

@[simp] lemma update_row_ne [decidable_eq n] {i' : n} (i_ne : i' ≠ i) :
  update_row M i b i' = M i' := function.update_noteq i_ne b M

@[simp] lemma update_column_ne [decidable_eq m] {j' : m} (j_ne : j' ≠ j) :
  update_column M j c i j' = M i j' := function.update_noteq j_ne (c i) (M i)

lemma update_row_apply [decidable_eq n] {i' : n} :
  update_row M i b i' j = if i' = i then b j else M i' j :=
begin
  by_cases i' = i,
  { rw [h, update_row_self, if_pos rfl] },
  { rwa [update_row_ne h, if_neg h] }
end

lemma update_column_apply [decidable_eq m] {j' : m} :
  update_column M j c i j' = if j' = j then c i else M i j' :=
begin
  by_cases j' = j,
  { rw [h, update_column_self, if_pos rfl] },
  { rwa [update_column_ne h, if_neg h] }
end

lemma update_row_transpose [decidable_eq m] : update_row Mᵀ j c = (update_column M j c)ᵀ :=
begin
  ext i' j,
  rw [transpose_apply, update_row_apply, update_column_apply],
  refl
end

lemma update_column_transpose [decidable_eq n] : update_column Mᵀ i b = (update_row M i b)ᵀ :=
begin
  ext i' j,
  rw [transpose_apply, update_row_apply, update_column_apply],
  refl
end

@[simp] lemma update_row_eq_self [decidable_eq m]
  (A : matrix m n α) {i : m} :
  A.update_row i (A i) = A :=
function.update_eq_self i A

@[simp] lemma update_column_eq_self [decidable_eq n]
  (A : matrix m n α) {i : n} :
  A.update_column i (λ j, A j i) = A :=
funext $ λ j, function.update_eq_self i (A j)

end update

section block_matrices

/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
def from_blocks (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  matrix (n ⊕ o) (l ⊕ m) α :=
sum.elim (λ i, sum.elim (A i) (B i))
         (λ i, sum.elim (C i) (D i))

@[simp] lemma from_blocks_apply₁₁
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : n) (j : l) :
  from_blocks A B C D (sum.inl i) (sum.inl j) = A i j :=
rfl

@[simp] lemma from_blocks_apply₁₂
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : n) (j : m) :
  from_blocks A B C D (sum.inl i) (sum.inr j) = B i j :=
rfl

@[simp] lemma from_blocks_apply₂₁
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : o) (j : l) :
  from_blocks A B C D (sum.inr i) (sum.inl j) = C i j :=
rfl

@[simp] lemma from_blocks_apply₂₂
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : o) (j : m) :
  from_blocks A B C D (sum.inr i) (sum.inr j) = D i j :=
rfl

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top left" submatrix. -/
def to_blocks₁₁ (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix n l α :=
λ i j, M (sum.inl i) (sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top right" submatrix. -/
def to_blocks₁₂ (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix n m α :=
λ i j, M (sum.inl i) (sum.inr j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom left" submatrix. -/
def to_blocks₂₁ (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix o l α :=
λ i j, M (sum.inr i) (sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom right" submatrix. -/
def to_blocks₂₂ (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix o m α :=
λ i j, M (sum.inr i) (sum.inr j)

lemma from_blocks_to_blocks (M : matrix (n ⊕ o) (l ⊕ m) α) :
  from_blocks M.to_blocks₁₁ M.to_blocks₁₂ M.to_blocks₂₁ M.to_blocks₂₂ = M :=
begin
  ext i j, rcases i; rcases j; refl,
end

@[simp] lemma to_blocks_from_blocks₁₁
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D).to_blocks₁₁ = A :=
rfl

@[simp] lemma to_blocks_from_blocks₁₂
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D).to_blocks₁₂ = B :=
rfl

@[simp] lemma to_blocks_from_blocks₂₁
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D).to_blocks₂₁ = C :=
rfl

@[simp] lemma to_blocks_from_blocks₂₂
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D).to_blocks₂₂ = D :=
rfl

lemma from_blocks_transpose
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D)ᵀ = from_blocks Aᵀ Cᵀ Bᵀ Dᵀ :=
begin
  ext i j, rcases i; rcases j; simp [from_blocks],
end

/-- Let `p` pick out certain rows and `q` pick out certain columns of a matrix `M`. Then
  `to_block M p q` is the corresponding block matrix. -/
def to_block (M : matrix m n α) (p : m → Prop) [decidable_pred p]
  (q : n → Prop) [decidable_pred q] : matrix {a // p a} {a // q a} α := M.minor coe coe

@[simp] lemma to_block_apply (M : matrix m n α) (p : m → Prop) [decidable_pred p]
  (q : n → Prop) [decidable_pred q] (i : {a // p a}) (j : {a // q a}) :
  to_block M p q i j = M ↑i ↑j := rfl

/-- Let `b` map rows and columns of a square matrix `M` to blocks. Then
  `to_square_block M b k` is the block `k` matrix. -/
def to_square_block (M : matrix m m α) {n : nat} (b : m → fin n) (k : fin n) :
  matrix {a // b a = k} {a // b a = k} α := M.minor coe coe

@[simp] lemma to_square_block_def (M : matrix m m α) {n : nat} (b : m → fin n) (k : fin n) :
  to_square_block M b k = λ i j, M ↑i ↑j := rfl

/-- Alternate version with `b : m → nat`. Let `b` map rows and columns of a square matrix `M` to
  blocks. Then `to_square_block' M b k` is the block `k` matrix. -/
def to_square_block' (M : matrix m m α) (b : m → nat) (k : nat) :
  matrix {a // b a = k} {a // b a = k} α := M.minor coe coe

@[simp] lemma to_square_block_def' (M : matrix m m α) (b : m → nat) (k : nat) :
  to_square_block' M b k = λ i j, M ↑i ↑j := rfl

/-- Let `p` pick out certain rows and columns of a square matrix `M`. Then
  `to_square_block_prop M p` is the corresponding block matrix. -/
def to_square_block_prop (M : matrix m m α) (p : m → Prop) [decidable_pred p] :
  matrix {a // p a} {a // p a} α := M.minor coe coe

@[simp] lemma to_square_block_prop_def (M : matrix m m α) (p : m → Prop) [decidable_pred p] :
  to_square_block_prop M p = λ i j, M ↑i ↑j := rfl

variables [semiring α]

lemma from_blocks_smul
  (x : α) (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  x • (from_blocks A B C D) = from_blocks (x • A) (x • B) (x • C) (x • D) :=
begin
  ext i j, rcases i; rcases j; simp [from_blocks],
end

lemma from_blocks_add
  (A  : matrix n l α) (B  : matrix n m α) (C  : matrix o l α) (D  : matrix o m α)
  (A' : matrix n l α) (B' : matrix n m α) (C' : matrix o l α) (D' : matrix o m α) :
  (from_blocks A B C D) + (from_blocks A' B' C' D') =
  from_blocks (A + A') (B + B')
              (C + C') (D + D') :=
begin
  ext i j, rcases i; rcases j; refl,
end

lemma from_blocks_multiply {p q : Type*} [fintype p] [fintype q]
  (A  : matrix n l α) (B  : matrix n m α) (C  : matrix o l α) (D  : matrix o m α)
  (A' : matrix l p α) (B' : matrix l q α) (C' : matrix m p α) (D' : matrix m q α) :
  (from_blocks A B C D) ⬝ (from_blocks A' B' C' D') =
  from_blocks (A ⬝ A' + B ⬝ C') (A ⬝ B' + B ⬝ D')
              (C ⬝ A' + D ⬝ C') (C ⬝ B' + D ⬝ D') :=
begin
  ext i j, rcases i; rcases j;
  simp only [from_blocks, mul_apply, fintype.sum_sum_type, sum.elim_inl, sum.elim_inr,
    pi.add_apply],
end

variables [decidable_eq l] [decidable_eq m]

@[simp] lemma from_blocks_diagonal (d₁ : l → α) (d₂ : m → α) :
  from_blocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (sum.elim d₁ d₂) :=
begin
  ext i j, rcases i; rcases j; simp [diagonal],
end

@[simp] lemma from_blocks_one : from_blocks (1 : matrix l l α) 0 0 (1 : matrix m m α) = 1 :=
by { ext i j, rcases i; rcases j; simp [one_apply] }

end block_matrices

section block_diagonal

variables (M N : o → matrix m n α) [decidable_eq o]

section has_zero

variables [has_zero α]

/-- `matrix.block_diagonal M` turns a homogenously-indexed collection of matrices
`M : o → matrix m n α'` into a `m × o`-by-`n × o` block matrix which has the entries of `M` along
the diagonal and zero elsewhere.

See also `matrix.block_diagonal'` if the matrices may not have the same size everywhere.
-/
def block_diagonal : matrix (m × o) (n × o) α
| ⟨i, k⟩ ⟨j, k'⟩ := if k = k' then M k i j else 0

lemma block_diagonal_apply (ik jk) :
  block_diagonal M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0 :=
by { cases ik, cases jk, refl }

@[simp]
lemma block_diagonal_apply_eq (i j k) :
  block_diagonal M (i, k) (j, k) = M k i j :=
if_pos rfl

lemma block_diagonal_apply_ne (i j) {k k'} (h : k ≠ k') :
  block_diagonal M (i, k) (j, k') = 0 :=
if_neg h

@[simp] lemma block_diagonal_transpose :
  (block_diagonal M)ᵀ = block_diagonal (λ k, (M k)ᵀ) :=
begin
  ext,
  simp only [transpose_apply, block_diagonal_apply, eq_comm],
  split_ifs with h,
  { rw h },
  { refl }
end

@[simp] lemma block_diagonal_zero :
  block_diagonal (0 : o → matrix m n α) = 0 :=
by { ext, simp [block_diagonal_apply] }

@[simp] lemma block_diagonal_diagonal [decidable_eq m] (d : o → m → α) :
  block_diagonal (λ k, diagonal (d k)) = diagonal (λ ik, d ik.2 ik.1) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  simp only [block_diagonal_apply, diagonal],
  split_ifs; finish
end

@[simp] lemma block_diagonal_one [decidable_eq m] [has_one α] :
  block_diagonal (1 : o → matrix m m α) = 1 :=
show block_diagonal (λ (_ : o), diagonal (λ (_ : m), (1 : α))) = diagonal (λ _, 1),
by rw [block_diagonal_diagonal]

end has_zero

@[simp] lemma block_diagonal_add [add_monoid α] :
  block_diagonal (M + N) = block_diagonal M + block_diagonal N :=
begin
  ext,
  simp only [block_diagonal_apply, add_apply],
  split_ifs; simp
end

@[simp] lemma block_diagonal_neg [add_group α] :
  block_diagonal (-M) = - block_diagonal M :=
begin
  ext,
  simp only [block_diagonal_apply, neg_apply],
  split_ifs; simp
end

@[simp] lemma block_diagonal_sub [add_group α] :
  block_diagonal (M - N) = block_diagonal M - block_diagonal N :=
by simp [sub_eq_add_neg]

@[simp] lemma block_diagonal_mul {p : Type*} [fintype p] [semiring α] (N : o → matrix n p α) :
  block_diagonal (λ k, M k ⬝ N k) = block_diagonal M ⬝ block_diagonal N :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  simp only [block_diagonal_apply, mul_apply, ← finset.univ_product_univ, finset.sum_product],
  split_ifs with h; simp [h]
end

@[simp] lemma block_diagonal_smul {R : Type*} [semiring R] [add_comm_monoid α] [module R α]
  (x : R) : block_diagonal (x • M) = x • block_diagonal M :=
by { ext, simp only [block_diagonal_apply, pi.smul_apply], split_ifs; simp }

end block_diagonal

section block_diagonal'

variables (M N : Π i, matrix (m' i) (n' i) α) [decidable_eq o]

section has_zero

variables [has_zero α]

/-- `matrix.block_diagonal' M` turns `M : Π i, matrix (m i) (n i) α` into a
`Σ i, m i`-by-`Σ i, n i` block matrix which has the entries of `M` along the diagonal
and zero elsewhere.

This is the dependently-typed version of `matrix.block_diagonal`. -/
def block_diagonal' : matrix (Σ i, m' i) (Σ i, n' i) α
| ⟨k, i⟩ ⟨k', j⟩ := if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0

lemma block_diagonal'_eq_block_diagonal (M : o → matrix m n α) {k k'} (i j) :
  block_diagonal M (i, k) (j, k') = block_diagonal' M ⟨k, i⟩ ⟨k', j⟩ :=
rfl

lemma block_diagonal'_minor_eq_block_diagonal (M : o → matrix m n α) :
  (block_diagonal' M).minor (prod.to_sigma ∘ prod.swap) (prod.to_sigma ∘ prod.swap) =
    block_diagonal M :=
matrix.ext $ λ ⟨k, i⟩ ⟨k', j⟩, rfl

lemma block_diagonal'_apply (ik jk) :
  block_diagonal' M ik jk = if h : ik.1 = jk.1 then
    M ik.1 ik.2 (cast (congr_arg n' h.symm) jk.2) else 0 :=
by { cases ik, cases jk, refl }

@[simp]
lemma block_diagonal'_apply_eq (k i j) :
  block_diagonal' M ⟨k, i⟩ ⟨k, j⟩ = M k i j :=
dif_pos rfl

lemma block_diagonal'_apply_ne {k k'} (i j) (h : k ≠ k') :
  block_diagonal' M ⟨k, i⟩ ⟨k', j⟩ = 0 :=
dif_neg h

@[simp] lemma block_diagonal'_transpose :
  (block_diagonal' M)ᵀ = block_diagonal' (λ k, (M k)ᵀ) :=
begin
  ext ⟨ii, ix⟩ ⟨ji, jx⟩,
  simp only [transpose_apply, block_diagonal'_apply, eq_comm],
  dsimp only,
  split_ifs with h₁ h₂ h₂,
  { subst h₁, refl, },
  { exact (h₂ h₁.symm).elim },
  { exact (h₁ h₂.symm).elim },
  { refl }
end

@[simp] lemma block_diagonal'_zero :
  block_diagonal' (0 : Π i, matrix (m' i) (n' i) α) = 0 :=
by { ext, simp [block_diagonal'_apply] }

@[simp] lemma block_diagonal'_diagonal [∀ i, decidable_eq (m' i)] (d : Π i, m' i → α) :
  block_diagonal' (λ k, diagonal (d k)) = diagonal (λ ik, d ik.1 ik.2) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  simp only [block_diagonal'_apply, diagonal],
  split_ifs; finish
end

@[simp] lemma block_diagonal'_one [∀ i, decidable_eq (m' i)] [has_one α] :
  block_diagonal' (1 : Π i, matrix (m' i) (m' i) α) = 1 :=
show block_diagonal' (λ (i : o), diagonal (λ (_ : m' i), (1 : α))) = diagonal (λ _, 1),
by rw [block_diagonal'_diagonal]

end has_zero

@[simp] lemma block_diagonal'_add [add_monoid α] :
  block_diagonal' (M + N) = block_diagonal' M + block_diagonal' N :=
begin
  ext,
  simp only [block_diagonal'_apply, add_apply],
  split_ifs; simp
end

@[simp] lemma block_diagonal'_neg [add_group α] :
  block_diagonal' (-M) = - block_diagonal' M :=
begin
  ext,
  simp only [block_diagonal'_apply, neg_apply],
  split_ifs; simp
end

@[simp] lemma block_diagonal'_sub [add_group α] :
  block_diagonal' (M - N) = block_diagonal' M - block_diagonal' N :=
by simp [sub_eq_add_neg]

@[simp] lemma block_diagonal'_mul {p : o → Type*} [Π i, fintype (p i)] [semiring α]
  (N : Π i, matrix (n' i) (p i) α) :
    block_diagonal' (λ k, M k ⬝ N k) = block_diagonal' M ⬝ block_diagonal' N :=
begin
  ext ⟨k, i⟩ ⟨k', j⟩,
  simp only [block_diagonal'_apply, mul_apply, ← finset.univ_sigma_univ, finset.sum_sigma],
  rw fintype.sum_eq_single k,
  { split_ifs; simp },
  { intros j' hj', exact finset.sum_eq_zero (λ _ _, by rw [dif_neg hj'.symm, zero_mul]) },
end

@[simp] lemma block_diagonal'_smul {R : Type*} [semiring R] [add_comm_monoid α] [module R α]
  (x : R) : block_diagonal' (x • M) = x • block_diagonal' M :=
by { ext, simp only [block_diagonal'_apply, pi.smul_apply], split_ifs; simp }

end block_diagonal'

end matrix

namespace ring_hom
variables [semiring α] [semiring β]

lemma map_matrix_mul (M : matrix m n α) (N : matrix n o α) (i : m) (j : o) (f : α →+* β) :
  f (matrix.mul M N i j) = matrix.mul (λ i j, f (M i j)) (λ i j, f (N i j)) i j :=
by simp [matrix.mul_apply, ring_hom.map_sum]

end ring_hom
