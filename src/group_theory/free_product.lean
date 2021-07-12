/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import algebra.free_monoid
import group_theory.congruence
import data.list.chain
import group_theory.group_action.End_hom
/-!
# The free product of groups or monoids

Given an `ι`-indexed family `M` of monoids, we define their free product (categorical coproduct)
`free_product M`. When `ι` and all `M i` have decidable equality, the free product bijects with the
type `word M` of reduced words. This bijection is constructed by defining an action of
`free_product M` on `word M`.

When `M i` are all groups, `free_product M` is also a group (and the coproduct in the category of
groups).

## Main definitions

- `free_product M`: the free product, defined as a quotient of a free monoid.
- `free_product.of {i} : M i →* free_product M`.
- `free_product.lift : (Π {i}, M i →* N) ≃ (free_product M →* N)`: the universal property.
- `free_product.word M`: the type of reduced words.
- `free_product.word.equiv M : free_product M ≃ word M`.

## Remarks

There are many answers to the question "what is the free product of a family `M` of monoids?", and
they are all equivalent but not obviously equivalent. We provide two answers. The first, almost
tautological answer is given by `free_product M`, which is a quotient of the type of words in the
alphabet `Σ i, M i`. It's straightforward to define and easy to prove its universal property. But
this answer is not completely satisfactory, because it's difficult to tell when two elements
`x y : free_product M` are distinct since `free_product M` is defined as a quotient.

The second, maximally efficient answer is given by `word M`. An element of `word M` is a word in the
alphabet `Σ i, { m : M i // m ≠ 1 }`, where no adjacent letters can share an index `i`. Since we
only work with reduced words, there is no need for quotienting, so it's easy to tell when two
elements are distinct. However it's not obvious that this is even a monoid!

We prove that every element of `free_product M` can be represented by a unique reduced word, i.e.
`free_product M` and `word M` are equivalent types. This means that `word M` can be given a monoid
structure, and it lets us tell when two elements of `free_product M` are distinct.

There is also a completely tautological, maximally inefficient answer given by
`algebra.category.Mon.colimits`. Whereas `free_product M` at least ensures that (any instance of)
associativity holds by reflexivity, in this answer associativity holds because of quotienting. Yet
another answer, which is constructively more satisfying, can be obtained by showing that
`free_product.rel` is confluent.

## References

[van der Waerden, *Free products of groups*][MR25465]

-/

variables {ι : Type*} (M : Π i : ι, Type*) [Π i, monoid (M i)]

/-- A relation on the free monoid on alphabet `Σ i, M i`, relating `⟨i, 1⟩` with `1` and
`⟨i, x⟩ * ⟨i, y⟩` with `⟨i, x * y⟩`. -/
inductive free_product.rel : free_monoid (Σ i, M i) → free_monoid (Σ i, M i) → Prop
| of_one (i : ι) : free_product.rel (free_monoid.of ⟨i, 1⟩) 1
| of_mul {i : ι} (x y : M i) : free_product.rel (free_monoid.of ⟨i, x⟩ * free_monoid.of ⟨i, y⟩)
  (free_monoid.of ⟨i, x * y⟩)

/-- The free product (categorical coproduct) of an indexed family of monoids. -/
@[derive [monoid, inhabited]]
def free_product : Type* := (con_gen (free_product.rel M)).quotient

namespace free_product

/-- The type of reduced words. A reduced word cannot contain a letter `1`, and no two adjacent
letters can come from the same summand. -/
def word : Type* := { l : list (Σ i, { m : M i // m ≠ 1 }) // (l.map sigma.fst).chain' (≠) }

variable {M}

/-- The inclusion of a summand into the free product. -/
def of {i : ι} : M i →* free_product M :=
{ to_fun   := λ x, con.mk' _ (free_monoid.of $ sigma.mk i x),
  map_one' := (con.eq _).mpr (con_gen.rel.of _ _ (free_product.rel.of_one i)),
  map_mul' := λ x y, eq.symm $ (con.eq _).mpr (con_gen.rel.of _ _ (free_product.rel.of_mul x y)) }

lemma of_apply {i} (m : M i) : of m = con.mk' _ (free_monoid.of $ sigma.mk i m) := rfl

variables {N : Type*} [monoid N]

/-- See note [partially-applied ext lemmas]. -/
@[ext] lemma ext_hom (f g : free_product M →* N) (h : ∀ i, f.comp (of : M i →* _) = g.comp of) :
  f = g :=
(monoid_hom.cancel_right con.mk'_surjective).mp $ free_monoid.hom_eq $ λ ⟨i, x⟩,
  by rw [monoid_hom.comp_apply, monoid_hom.comp_apply, ←of_apply,
    ←monoid_hom.comp_apply, ←monoid_hom.comp_apply, h]

/-- A map out of the free product corresponds to a family of maps out of the summands. This is the
universal property of the free product, charaterizing it as a categorical coproduct. -/
@[simps symm_apply]
def lift : (Π i, M i →* N) ≃ (free_product M →* N) :=
{ to_fun := λ fi, con.lift _ (free_monoid.lift $ λ p : Σ i, M i, fi p.fst p.snd) $ con.con_gen_le
    begin
      simp_rw [con.rel_eq_coe, con.ker_rel],
      rintros _ _ (i | ⟨i, x, y⟩),
      { change free_monoid.lift _ (free_monoid.of _) = free_monoid.lift _ 1,
        simp only [monoid_hom.map_one, free_monoid.lift_eval_of], },
      { change free_monoid.lift _ (free_monoid.of _ * free_monoid.of _) =
          free_monoid.lift _ (free_monoid.of _),
        simp only [monoid_hom.map_mul, free_monoid.lift_eval_of], }
    end,
  inv_fun := λ f i, f.comp of,
  left_inv := by { intro fi, ext i x,
    rw [monoid_hom.comp_apply, of_apply, con.lift_mk', free_monoid.lift_eval_of], },
  right_inv := by { intro f, ext i x,
    simp only [monoid_hom.comp_apply, of_apply, con.lift_mk', free_monoid.lift_eval_of], } }

@[simp] lemma lift_of {N} [monoid N] (fi : Π i, M i →* N) {i} (m : M i) :
  lift fi (of m) = fi i m :=
by conv_rhs { rw [←lift.symm_apply_apply fi, lift_symm_apply, monoid_hom.comp_apply] }

lemma induction_on {C : free_product M → Prop}
  (m : free_product M)
  (h_one : C 1)
  (h_of : ∀ {i} (m : M i), C (of m))
  (h_mul : ∀ {x y}, C x → C y → C (x * y)) :
  C m :=
begin
  apply con.induction_on m,
  intro m',
  apply m'.rec_on,
  { rw con.coe_one, exact h_one, },
  { rintros ⟨i, x⟩ m'' ih, rw con.coe_mul, exact h_mul (h_of x) ih },
end

section group

variables (G : ι → Type*) [∀ i, group (G i)]

instance : has_inv (free_product G) :=
{ inv := opposite.unop ∘ lift (λ i, (of : G i →* _).op.comp (mul_equiv.inv' (G i)).to_monoid_hom) }

lemma inv_def (x : free_product G) : x⁻¹ = opposite.unop
  (lift (λ i, (of : G i →* _).op.comp (mul_equiv.inv' (G i)).to_monoid_hom) x) := rfl

instance : group (free_product G) :=
{ mul_left_inv := begin
    intro m,
    rw inv_def,
    apply m.induction_on,
    { rw [monoid_hom.map_one, opposite.unop_one, one_mul], },
    { intros i m, change of m⁻¹ * of m = 1, rw [←of.map_mul, mul_left_inv, of.map_one], },
    { intros x y hx hy,
      rw [monoid_hom.map_mul, opposite.unop_mul, mul_assoc, ←mul_assoc _ x y, hx, one_mul, hy], },
  end,
  ..free_product.has_inv G,
  ..free_product.monoid G }

end group

namespace word

/-- The empty reduced word. -/
def empty : word M := ⟨[], list.chain'_nil⟩

instance : inhabited (word M) := ⟨empty⟩

/-- A reduced word determines an element of the free product, given by multiplication. -/
def prod (w : word M) : free_product M :=
list.prod (w.val.map $ λ p, of p.snd.val)

@[simp] lemma prod_nil : (empty : word M).prod = 1 := rfl

variables [∀ i, decidable_eq (M i)]

/-- Prepend `m : M i` to `w` assuming `i` is not the first index in `w`. If `m = 1`, do nothing. -/
def rcons {i} (m : M i) (w : word M) (h : ∀ p ∈ (w.val.map sigma.fst).head', i ≠ p) : word M :=
if m_one : m = 1 then w else ⟨⟨i, m, m_one⟩ :: w.val, w.property.cons' h⟩

@[simp] lemma rcons_one {i} (w : word M) (h) : rcons (1 : M i) w h = w := dif_pos rfl

lemma rcons_ne_one {i} {m : M i} (hm : m ≠ 1) {w : word M} (h) :
  rcons m w h = ⟨⟨i, m, hm⟩ :: w.val, w.property.cons' h⟩ := dif_neg hm

lemma cons_eq_rcons {i m ls hl} :
  (⟨⟨i, m⟩ :: ls, hl⟩ : word M) = rcons m.val ⟨ls, hl.tail⟩ hl.rel_head' :=
by { cases m with m hm, rw rcons_ne_one hm, refl, }

@[simp] lemma rcons_prod {i} (m : M i) (w h) :
  (rcons m w h).prod = of m * w.prod :=
if hm : m = 1 then by rw [hm, rcons_one, monoid_hom.map_one, one_mul]
else by rw [rcons_ne_one hm, prod, list.map_cons, list.prod_cons, prod]

variable [decidable_eq ι]

/-- A custom eliminator for the free product. The idea is that any reduced word can be uniquely
expressed as `rcons m w h` with `m : M i`. If `i` is not the word's first index then `m = 1`. -/
def cases {i : ι} (C : word M → Sort*)
  (d : Π (m : M i) (w : word M) (h), C (rcons m w h)) :
  Π w : word M, C w
| w@⟨[], _⟩ := @eq.rec _ _ C (d 1 w $ by rintro _ ⟨⟩) _ (rcons_one w _)
| w@⟨⟨j, m⟩ :: ls, h⟩ := if ij : i = j then by { cases ij, rw cons_eq_rcons, apply d, }
else @eq.rec _ _ C (d 1 w $ by { rintro _ ⟨⟩, exact ij }) _ (rcons_one w _)

/-- Computation rule for `free_product.cases` in the non-dependent case. -/
@[simp] lemma cases_def {i : ι} {C : Sort*} {d} (m : M i) (w : word M) (h) :
  (rcons m w h).cases (λ _, C) d = d m w h :=
begin
  by_cases hm : m = 1,
  { rw [hm, rcons_one],
    rcases w with ⟨⟨⟩ | ⟨⟨j, m'⟩, ls⟩, hl ⟩,
    { rw [word.cases, eq_rec_constant]},
    { rw [word.cases, dif_neg (h j rfl), eq_rec_constant], }, },
  { rw [rcons_ne_one hm, word.cases, dif_pos rfl], cases w, refl, },
end

instance summand_action (i) : mul_action (M i) (word M) :=
{ smul     := λ m w, w.cases _ $ λ m' w' h, rcons (m * m') w' h,
  one_smul := λ w, w.cases _ $ λ m' w' h, by { dsimp only, rw [cases_def, one_mul] },
  mul_smul := λ m m' w, w.cases _ $ λ m'' w' h,
    by { dsimp only, rw [cases_def, cases_def, cases_def, mul_assoc] } }

instance : mul_action (free_product M) (word M) :=
mul_action.of_End_hom (lift (λ i, mul_action.to_End_hom))

lemma smul_rcons (i) (m m' : M i) (w h) : of m • rcons m' w h = rcons (m * m') w h :=
cases_def m' w h

lemma cons_eq_smul {i m ls hl} :
  (⟨⟨i, m⟩ :: ls, hl⟩ : word M) = (of m.val • ⟨ls, hl.tail⟩ : word M) :=
by rw [←rcons_one ⟨ls, hl.tail⟩ hl.rel_head', smul_rcons, mul_one, cons_eq_rcons]

lemma smul_induction {C : word M → Prop}
  (h_empty : C empty)
  (h_smul : ∀ i (m : M i) w, C w → C (of m • w))
  (w : word M) : C w :=
begin
  cases w with ls hl,
  induction ls with p ls ih,
  { exact h_empty },
  cases p with i m,
  rw cons_eq_smul,
  exact h_smul i m.val _ (ih _),
end

@[simp] lemma smul_prod (m) : ∀ w : word M, (m • w).prod = m * w.prod :=
m.induction_on
(λ w, by rw [one_smul, one_mul])
(λ i m w, w.cases _ $ λ m' w' h,
  by rw [smul_rcons, rcons_prod, rcons_prod, of.map_mul, mul_assoc])
(λ x y hx hy w, by rw [mul_smul, hx, hy, mul_assoc])

/-- An element of the free product corresponds to a unique reduced word. -/
def equiv : free_product M ≃ word M :=
{ to_fun := λ m, m • empty,
  inv_fun := λ w, w.prod,
  left_inv := begin
    intro m,
    dsimp only,
    rw [smul_prod, prod_nil, mul_one],
  end,
  right_inv := begin
    apply smul_induction,
    { dsimp only, rw [prod_nil, one_smul], },
    { dsimp only,
      intros i m w ih,
      rw [smul_prod, mul_smul, ih], },
  end }

end word

end free_product
