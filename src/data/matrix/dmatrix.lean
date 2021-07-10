/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype.basic

/-!
# Matrices
-/
universes u u' v w z

/-- `dmatrix m n` is the type of dependently typed matrices
whose rows are indexed by the fintype `m` and
whose columns are indexed by the fintype `n`. -/
@[nolint unused_arguments]
def dmatrix (m : Type u) (n : Type u') [fintype m] [fintype n] (α : m → n → Type v) :
  Type (max u u' v) :=
Π i j, α i j

variables {l m n o : Type*} [fintype l] [fintype m] [fintype n] [fintype o]
variables {α : m → n → Type v}

namespace dmatrix

section ext
variables {M N : dmatrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
⟨λ h, funext $ λ i, funext $ h i, λ h, by simp [h]⟩

@[ext] theorem ext : (∀ i j, M i j = N i j) → M = N :=
ext_iff.mp

end ext

/-- `M.map f` is the dmatrix obtained by applying `f` to each entry of the matrix `M`. -/
def map (M : dmatrix m n α) {β : m → n → Type w} (f : Π ⦃i j⦄, α i j → β i j) :
  dmatrix m n β := λ i j, f (M i j)

@[simp]
lemma map_apply {M : dmatrix m n α} {β : m → n → Type w} {f : Π ⦃i j⦄, α i j → β i j}
  {i : m} {j : n} : M.map f i j = f (M i j) :=
rfl

@[simp]
lemma map_map {M : dmatrix m n α} {β : m → n → Type w} {γ : m → n → Type z}
  {f : Π ⦃i j⦄, α i j → β i j} {g : Π ⦃i j⦄, β i j → γ i j} :
  (M.map f).map g = M.map (λ i j x, g (f x)) :=
by { ext, simp, }

/-- The transpose of a dmatrix. -/
def transpose (M : dmatrix m n α) : dmatrix n m (λ j i, α i j)
| x y := M y x

localized "postfix `ᵀ`:1500 := dmatrix.transpose" in dmatrix

/-- `dmatrix.col u` is the column matrix whose entries are given by `u`. -/
def col {α : m → Type v} (w : Π i, α i) : dmatrix m unit (λ i j, α i)
| x y := w x

/-- `dmatrix.row u` is the row matrix whose entries are given by `u`. -/
def row {α : n → Type v} (v : Π j, α j) : dmatrix unit n (λ i j, α j)
| x y := v y

instance [∀ i j, inhabited (α i j)] : inhabited (dmatrix m n α) := pi.inhabited _
instance [∀ i j, has_add (α i j)] : has_add (dmatrix m n α) := pi.has_add
instance [∀ i j, add_semigroup (α i j)] : add_semigroup (dmatrix m n α) := pi.add_semigroup
instance [∀ i j, add_comm_semigroup (α i j)] : add_comm_semigroup (dmatrix m n α) :=
pi.add_comm_semigroup
instance [∀ i j, has_zero (α i j)] : has_zero (dmatrix m n α) := pi.has_zero
instance [∀ i j, add_monoid (α i j)] : add_monoid (dmatrix m n α) := pi.add_monoid
instance [∀ i j, add_comm_monoid (α i j)] : add_comm_monoid (dmatrix m n α) := pi.add_comm_monoid
instance [∀ i j, has_neg (α i j)] : has_neg (dmatrix m n α) := pi.has_neg
instance [∀ i j, has_sub (α i j)] : has_sub (dmatrix m n α) := pi.has_sub
instance [∀ i j, add_group (α i j)] : add_group (dmatrix m n α) := pi.add_group
instance [∀ i j, add_comm_group (α i j)] : add_comm_group (dmatrix m n α) := pi.add_comm_group
instance [∀ i j, unique (α i j)] : unique (dmatrix m n α) := pi.unique
instance [∀ i j, subsingleton (α i j)] : subsingleton (dmatrix m n α) := pi.subsingleton

@[simp] theorem zero_apply [∀ i j, has_zero (α i j)] (i j) : (0 : dmatrix m n α) i j = 0 := rfl
@[simp] theorem neg_apply [∀ i j, has_neg (α i j)] (M : dmatrix m n α) (i j) :
  (- M) i j = - M i j :=
rfl
@[simp] theorem add_apply [∀ i j, has_add (α i j)] (M N : dmatrix m n α) (i j) :
  (M + N) i j = M i j + N i j :=
rfl
@[simp] theorem sub_apply [∀ i j, has_sub (α i j)] (M N : dmatrix m n α) (i j) :
  (M - N) i j = M i j - N i j :=
rfl

@[simp] lemma map_zero [∀ i j, has_zero (α i j)] {β : m → n → Type w} [∀ i j, has_zero (β i j)]
  {f : Π ⦃i j⦄, α i j → β i j} (h : ∀ i j, f (0 : α i j) = 0) :
  (0 : dmatrix m n α).map f = 0 :=
by { ext, simp [h], }

lemma map_add [∀ i j, add_monoid (α i j)] {β : m → n → Type w} [∀ i j, add_monoid (β i j)]
  (f : Π ⦃i j⦄, α i j →+ β i j) (M N : dmatrix m n α) :
  (M + N).map (λ i j, @f i j) = M.map (λ i j, @f i j) + N.map (λ i j, @f i j) :=
by { ext, simp, }

lemma map_sub [∀ i j, add_group (α i j)] {β : m → n → Type w} [∀ i j, add_group (β i j)]
  (f : Π ⦃i j⦄, α i j →+ β i j) (M N : dmatrix m n α) :
  (M - N).map (λ i j, @f i j) = M.map (λ i j, @f i j) - N.map (λ i j, @f i j) :=
by { ext, simp }

-- TODO[gh-6025]: make this an instance once safe to do so
lemma subsingleton_of_empty_left [is_empty m] : subsingleton (dmatrix m n α) :=
⟨λ M N, by { ext, exact is_empty_elim i }⟩

-- TODO[gh-6025]: make this an instance once safe to do so
lemma subsingleton_of_empty_right [is_empty n] : subsingleton (dmatrix m n α) :=
⟨λ M N, by { ext, exact is_empty_elim j }⟩

end dmatrix

/-- The `add_monoid_hom` between spaces of dependently typed matrices
induced by an `add_monoid_hom` between their coefficients. -/
def add_monoid_hom.map_dmatrix
  [∀ i j, add_monoid (α i j)] {β : m → n → Type w} [∀ i j, add_monoid (β i j)]
  (f : Π ⦃i j⦄, α i j →+ β i j) :
  dmatrix m n α →+ dmatrix m n β :=
{ to_fun := λ M, M.map (λ i j, @f i j),
  map_zero' := by simp,
  map_add' := dmatrix.map_add f, }

@[simp] lemma add_monoid_hom.map_dmatrix_apply
  [∀ i j, add_monoid (α i j)] {β : m → n → Type w} [∀ i j, add_monoid (β i j)]
  (f : Π ⦃i j⦄, α i j →+ β i j) (M : dmatrix m n α) :
  add_monoid_hom.map_dmatrix f M = M.map (λ i j, @f i j) :=
rfl
