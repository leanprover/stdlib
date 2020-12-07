/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/

import data.equiv.fin

/-!
# Finite tuples, implemented as functions on `fin n`.

The main advantage of `tuple` over alternatives like `vector` is that
extracting coordinates (components) of a `tuple` is just function application.

## Main definitions

* `tuple α n` is by definition the type `fin n → α`. We think of it as
  the `n`-fold product `αⁿ` and imagine a value `x : tuple α n` as
  representing a vector `(x 0, ..., x (n-1))`.
* `tuple.append`, `tuple.left` and `tuple.right` together exhibit the
  isomorphism `αⁿ⁺ᵐ ≅ αⁿ × αᵐ`.
* `tuple.snoc`, `tuple.init` and `tuple.last` likewise exhibit the
  isomorphism `αⁿ⁺¹ ≅ αⁿ × α`.
-/

/-- A (homogeneous) `n`-tuple `α`s, implemented as a function from `fin n`.
The `j`th component of such a tuple `x` (where `j : fin n`) is simply `x j`.

This definition is marked `reducible` because we really want to think of
`x : tuple α n` as a function, while writing the type as `tuple` in order
to support `.` notation. In particular, this means instances for `ι → α`
also match `tuple α n` (with `ι = fin n`). -/
@[reducible] def tuple (α : Type*) (n : ℕ) : Type* := fin n → α

namespace tuple

variables {α : Type*}

def nil : tuple α 0 :=
fin_zero_elim

instance : unique (tuple α 0) :=
⟨⟨nil⟩, by { intro x, ext i, exact fin_zero_elim i }⟩

/-- Transport a vector across an equality of dimensions.
This is implemented without using `eq.rec` so that it will reduce
when evaluated at a constructor `⟨j, h : j < n'⟩` of `fin n'`. -/
protected def cast {n n' : ℕ} (h : n = n') : tuple α n → tuple α n' :=
λ x j, x (j.cast h.symm)

@[simp] lemma cast_app {n n' : ℕ} {h : n = n'} {x : tuple α n} {j : fin n'} :
  (x.cast h) j = x (j.cast h.symm) :=
rfl

@[simp] lemma cast_id {n : ℕ} {h : n = n} {x : tuple α n} : x.cast h = x :=
by { ext ⟨i, _⟩, refl }

section prod

/-! ### Products

The isomorphism αⁿ⁺ᵐ ≅ αⁿ × αᵐ is ubiquitous in mathematics, and usually
invoked implicitly. Lean maintains a distinction between the two sides of course.
Here, we provide an API which presents `tuple α (n+m)` as though it were
a structure with two fields, `left : tuple α n` and `right : tuple α m`,
constructor `append : tuple α n → tuple α m → tuple α (n+m)`,
and corresponding recursion principle `prod_rec`.

The arguments `n m : ℕ` are implicit throughout this API, to be inferred
from the argument or result types; this may seem problematic, since a number
can be written in the form `n+m` in many ways, but actually works well
in practice. -/

variables {n m : ℕ}

/-- Project `αⁿ⁺ᵐ ≅ αⁿ × αᵐ` to the first factor. -/
protected def left : tuple α (n + m) → tuple α n :=
λ x j, x (fin.cast_add m j)

/-- Project `αⁿ⁺ᵐ ≅ αⁿ × αᵐ` to the second factor. -/
protected def right : tuple α (n + m) → tuple α m :=
λ x j, x (fin.nat_add n j)

/-- The canonical equivalence `αⁿ⁺ᵐ ≅ αⁿ × αᵐ`. -/
def append_equiv : tuple α (n + m) ≃ tuple α n × tuple α m :=
calc  (fin (n + m) → α)
    ≃ (fin n ⊕ fin m → α)        : equiv.arrow_congr sum_fin_sum_equiv.symm (equiv.refl _)
... ≃ (fin n → α) × (fin m → α)  : (equiv.sum_arrow_equiv_prod_arrow (fin n) (fin m) α)

/-- The concatenation of two `tuple`s. -/
def append (x : tuple α n) (y : tuple α m) : tuple α (n + m) :=
append_equiv.symm (x, y)

localized "infixr ` ++ ` := tuple.append" in tuple

lemma append_equiv_app {z : tuple α (n + m)} : append_equiv z = (z.left, z.right) := rfl

lemma append_equiv_symm_app {x : tuple α n} {y : tuple α m} :
  append_equiv.symm (x, y) = x ++ y :=
rfl

@[simp] lemma left_append_right (x : tuple α (n + m)) : x.left ++ x.right = x :=
append_equiv.symm_apply_apply x

@[simp] lemma left_append {x : tuple α n} {y : tuple α m} : (x ++ y).left = x :=
congr_arg prod.fst (append_equiv.apply_symm_apply (x, y) : _)

@[simp] lemma right_append {x : tuple α n} {y : tuple α m} : (x ++ y).right = y :=
congr_arg prod.snd (append_equiv.apply_symm_apply (x, y) : _)

lemma prod_ext {z z' : tuple α (n + m)} :
  z = z' ↔ z.left = z'.left ∧ z.right = z'.right :=
append_equiv.apply_eq_iff_eq.symm.trans prod.mk.inj_iff

lemma append.inj_iff {x x' : tuple α n} {y y' : tuple α m} :
  x ++ y = x' ++ y' ↔ x = x' ∧ y = y' :=
by simp only [append, equiv.apply_eq_iff_eq, prod.mk.inj_iff]

lemma left_zero {x : tuple α (n + 0)} : x.left = x :=
by { ext ⟨_, _⟩, refl }

lemma right_zero {x : tuple α (0 + n)} : x.right = x.cast (zero_add n) :=
funext $ λ _, congr_arg x (by rw fin.nat_add_zero)

@[simp] lemma append_zero {x : tuple α n} {y : tuple α 0} : x ++ y = x :=
begin
  rw [prod_ext, left_append, left_zero, right_append],
  exact ⟨rfl, subsingleton.elim _ _⟩
end

/-- Recursion principle for `tuple (n + m) α`,
imagined as a structure containing its left and right parts. -/
@[elab_as_eliminator]
def prod_rec {C : tuple α (n + m) → Sort*}
  (h : Π (x : tuple α n) (y : tuple α m), C (x ++ y)) (z : tuple α (n + m)) : C z :=
by { rw ← left_append_right z, exact h z.left z.right }

lemma prod_rec_beta {C : tuple α (n + m) → Sort*}
  (h : Π (x : tuple α n) (y : tuple α m), C (x ++ y)) (x : tuple α n) (y : tuple α m) :
  (x.append y).prod_rec h = h x y :=
by { apply eq_of_heq, refine (eq_mpr_heq _ _).trans _, rw [left_append, right_append] }

end prod

section snoc

/-! ### Appending a single element (snoc)

This section is parallel to the `prod` section but based on the isomorphism αⁿ⁺¹ ≅ αⁿ × α.
We name the projections `init : tuple α (n+1) → tuple α n`
(which equals `left` specialized to `m = 1`) and `last : tuple α (n+1) → α`,
with constructor `snoc : tuple α n → α → tuple α (n+1)` and
corresponding recursion principle `snoc_rec`. -/

variables {n : ℕ}

/-- All but the last coordinate of a `tuple`. -/
protected def init : tuple α (n + 1) → tuple α n :=
λ x j, x (fin.cast_succ j)

lemma left_eq_init {x : tuple α (n + 1)} : x.left = x.init := rfl

/-- The last coordinate of a `tuple`. -/
protected def last : tuple α (n + 1) → α :=
λ x, x (fin.last n)

/-- The canonical equivalence `αⁿ⁺¹ ≅ αⁿ × α`. -/
def snoc_equiv : tuple α (n + 1) ≃ tuple α n × α :=
calc  (fin (n + 1) → α)
    ≃ (fin n → α) × (fin 1 → α)  : append_equiv
... ≃ (fin n → α) × α            : equiv.prod_congr (equiv.refl _) (equiv.fun_unique (fin 1) α)

/-- Form a `tuple` by appending a single coordinate to an existing `tuple`. -/
def snoc (x : tuple α n) (a : α) : tuple α (n + 1) :=
snoc_equiv.symm (x, a)

lemma snoc_equiv_app {z : tuple α (n + 1)} : snoc_equiv z = (z.init, z.last) := rfl

lemma snoc_equiv_symm_app {x : tuple α n} {a : α} :
  snoc_equiv.symm (x, a) = x.snoc a :=
rfl

@[simp] lemma init_snoc_last (x : tuple α (n + 1)) : x.init.snoc x.last = x :=
snoc_equiv.symm_apply_apply x

@[simp] lemma init_snoc {x : tuple α n} {a : α} : (x.snoc a).init = x :=
congr_arg prod.fst (snoc_equiv.apply_symm_apply (x, a) : _)

@[simp] lemma last_snoc {x : tuple α n} {a : α} : (x.snoc a).last = a :=
congr_arg prod.snd (snoc_equiv.apply_symm_apply (x, a) : _)

lemma snoc.inj_iff {x x' : tuple α n} {a a' : α} :
  x.snoc a = x'.snoc a' ↔ x = x' ∧ a = a' :=
by simp only [snoc, equiv.apply_eq_iff_eq, prod.mk.inj_iff]

/-- Recursion principle for `tuple (n + 1) α`,
imagined as a structure containing its initial part and last coordinate. -/
@[elab_as_eliminator]
def snoc_rec {C : tuple α (n + 1) → Sort*}
  (h : Π (x : tuple α n) (a : α), C (snoc x a)) (z : tuple α (n + 1)) : C z :=
by { rw ← init_snoc_last z, exact h z.init z.last }

lemma snoc_rec_beta {C : tuple α (n + 1) → Sort*}
  (h : Π (x : tuple α n) (a : α), C (snoc x a)) (x : tuple α n) (a : α) :
  (x.snoc a).snoc_rec h = h x a :=
by { apply eq_of_heq, refine (eq_mpr_heq _ _).trans _, rw [init_snoc, last_snoc] }

end snoc

end tuple
