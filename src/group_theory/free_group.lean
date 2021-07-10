/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.fintype.basic
import group_theory.subgroup

/-!
# Free groups

This file defines free groups over a type. Furthermore, it is shown that the free group construction
is an instance of a monad. For the result that `free_group` is the left adjoint to the forgetful
functor from groups to types, see `algebra/category/Group/adjunctions`.

## Main definitions

* `free_group`: the free group associated to a type `α` defined as the words over `a : α × bool `
  modulo the relation `a * x * x⁻¹ * b = a * b`.
* `mk`: the canonical quotient map `list (α × bool) → free_group α`.
* `of`: the canoical injection `α → free_group α`.
* `lift f`: the canonical group homomorphism `free_group α →* G` given a group `G` and a
  function `f : α → G`.

## Main statements

* `church_rosser`: The Church-Rosser theorem for word reduction (also known as Newman's diamond
  lemma).
* `free_group_unit_equiv_int`: The free group over the one-point type is isomorphic to the integers.
* The free group construction is an instance of a monad.

## Implementation details

First we introduce the one step reduction relation `free_group.red.step`:
`w * x * x⁻¹ * v   ~>   w * v`, its reflexive transitive closure `free_group.red.trans`
and prove that its join is an equivalence relation. Then we introduce `free_group α` as a quotient
over `free_group.red.step`.

## Tags

free group, Newman's diamond lemma, Church-Rosser theorem
-/

open relation

universes u v w

variables {α : Type u}

local attribute [simp] list.append_eq_has_append

namespace free_group
variables {L L₁ L₂ L₃ L₄ : list (α × bool)}

/-- Reduction step: `w * x * x⁻¹ * v ~> w * v` -/
inductive red.step : list (α × bool) → list (α × bool) → Prop
| bnot {L₁ L₂ x b} : red.step (L₁ ++ (x, b) :: (x, bnot b) :: L₂) (L₁ ++ L₂)
attribute [simp] red.step.bnot

/-- Reflexive-transitive closure of red.step -/
def red : list (α × bool) → list (α × bool) → Prop := refl_trans_gen red.step

@[refl] lemma red.refl : red L L := refl_trans_gen.refl
@[trans] lemma red.trans : red L₁ L₂ → red L₂ L₃ → red L₁ L₃ := refl_trans_gen.trans

namespace red

/-- Predicate asserting that word `w₁` can be reduced to `w₂` in one step, i.e. there are words
`w₃ w₄` and letter `x` such that `w₁ = w₃xx⁻¹w₄` and `w₂ = w₃w₄`  -/
theorem step.length : ∀ {L₁ L₂ : list (α × bool)}, step L₁ L₂ → L₂.length + 2 = L₁.length
| _ _ (@red.step.bnot _ L1 L2 x b) := by rw [list.length_append, list.length_append]; refl

@[simp] lemma step.bnot_rev {x b} : step (L₁ ++ (x, bnot b) :: (x, b) :: L₂) (L₁ ++ L₂) :=
by cases b; from step.bnot

@[simp] lemma step.cons_bnot {x b} : red.step ((x, b) :: (x, bnot b) :: L) L :=
@step.bnot _ [] _ _ _

@[simp] lemma step.cons_bnot_rev {x b} : red.step ((x, bnot b) :: (x, b) :: L) L :=
@red.step.bnot_rev _ [] _ _ _

theorem step.append_left : ∀ {L₁ L₂ L₃ : list (α × bool)}, step L₂ L₃ → step (L₁ ++ L₂) (L₁ ++ L₃)
| _ _ _ red.step.bnot := by rw [← list.append_assoc, ← list.append_assoc]; constructor

theorem step.cons {x} (H : red.step L₁ L₂) : red.step (x :: L₁) (x :: L₂) :=
@step.append_left _ [x] _ _ H

theorem step.append_right : ∀ {L₁ L₂ L₃ : list (α × bool)}, step L₁ L₂ → step (L₁ ++ L₃) (L₂ ++ L₃)
| _ _ _ red.step.bnot := by simp

lemma not_step_nil : ¬ step [] L :=
begin
  generalize h' : [] = L',
  assume h,
  cases h with L₁ L₂,
  simp [list.nil_eq_append_iff] at h',
  contradiction
end

lemma step.cons_left_iff {a : α} {b : bool} :
  step ((a, b) :: L₁) L₂ ↔ (∃L, step L₁ L ∧ L₂ = (a, b) :: L) ∨ (L₁ = (a, bnot b)::L₂) :=
begin
  split,
  { generalize hL : ((a, b) :: L₁ : list _) = L,
    assume h,
    rcases h with ⟨_ | ⟨p, s'⟩, e, a', b'⟩,
    { simp at hL, simp [*] },
    { simp at hL,
      rcases hL with ⟨rfl, rfl⟩,
      refine or.inl ⟨s' ++ e, step.bnot, _⟩,
      simp } },
  { assume h,
    rcases h with ⟨L, h, rfl⟩ | rfl,
    { exact step.cons h },
    { exact step.cons_bnot } }
end

lemma not_step_singleton : ∀ {p : α × bool}, ¬ step [p] L
| (a, b) := by simp [step.cons_left_iff, not_step_nil]

lemma step.cons_cons_iff : ∀{p : α × bool}, step (p :: L₁) (p :: L₂) ↔ step L₁ L₂ :=
by simp [step.cons_left_iff, iff_def, or_imp_distrib] {contextual := tt}

lemma step.append_left_iff : ∀L, step (L ++ L₁) (L ++ L₂) ↔ step L₁ L₂
| [] := by simp
| (p :: l) := by simp [step.append_left_iff l, step.cons_cons_iff]

private theorem step.diamond_aux : ∀ {L₁ L₂ L₃ L₄ : list (α × bool)} {x1 b1 x2 b2},
  L₁ ++ (x1, b1) :: (x1, bnot b1) :: L₂ = L₃ ++ (x2, b2) :: (x2, bnot b2) :: L₄ →
  L₁ ++ L₂ = L₃ ++ L₄ ∨ ∃ L₅, red.step (L₁ ++ L₂) L₅ ∧ red.step (L₃ ++ L₄) L₅
| []        _ []        _ _ _ _ _ H := by injections; subst_vars; simp
| []        _ [(x3,b3)] _ _ _ _ _ H := by injections; subst_vars; simp
| [(x3,b3)] _ []        _ _ _ _ _ H := by injections; subst_vars; simp
| []                     _ ((x3,b3)::(x4,b4)::tl) _ _ _ _ _ H :=
  by injections; subst_vars; simp; right; exact ⟨_, red.step.bnot, red.step.cons_bnot⟩
| ((x3,b3)::(x4,b4)::tl) _ []                     _ _ _ _ _ H :=
  by injections; subst_vars; simp; right; exact ⟨_, red.step.cons_bnot, red.step.bnot⟩
| ((x3,b3)::tl) _ ((x4,b4)::tl2) _ _ _ _ _ H :=
  let ⟨H1, H2⟩ := list.cons.inj H in
  match step.diamond_aux H2 with
    | or.inl H3 := or.inl $ by simp [H1, H3]
    | or.inr ⟨L₅, H3, H4⟩ := or.inr
      ⟨_, step.cons H3, by simpa [H1] using step.cons H4⟩
  end

theorem step.diamond : ∀ {L₁ L₂ L₃ L₄ : list (α × bool)},
  red.step L₁ L₃ → red.step L₂ L₄ → L₁ = L₂ →
  L₃ = L₄ ∨ ∃ L₅, red.step L₃ L₅ ∧ red.step L₄ L₅
| _ _ _ _ red.step.bnot red.step.bnot H := step.diamond_aux H

lemma step.to_red : step L₁ L₂ → red L₁ L₂ :=
refl_trans_gen.single

/-- **Church-Rosser theorem** for word reduction: If `w1 w2 w3` are words such that `w1` reduces
to `w2` and `w3` respectively, then there is a word `w4` such that `w2` and `w3` reduce to `w4`
respectively. This is also known as Newman's diamond lemma. -/
theorem church_rosser : red L₁ L₂ → red L₁ L₃ → join red L₂ L₃ :=
relation.church_rosser (assume a b c hab hac,
match b, c, red.step.diamond hab hac rfl with
| b, _, or.inl rfl           := ⟨b, by refl, by refl⟩
| b, c, or.inr ⟨d, hbd, hcd⟩ := ⟨d, refl_gen.single hbd, hcd.to_red⟩
end)

lemma cons_cons {p} : red L₁ L₂ → red (p :: L₁) (p :: L₂) :=
refl_trans_gen_lift (list.cons p) (assume a b, step.cons)

lemma cons_cons_iff (p) : red (p :: L₁) (p :: L₂) ↔ red L₁ L₂ :=
iff.intro
  begin
    generalize eq₁ : (p :: L₁ : list _) = LL₁,
    generalize eq₂ : (p :: L₂ : list _) = LL₂,
    assume h,
    induction h using relation.refl_trans_gen.head_induction_on
      with L₁ L₂ h₁₂ h ih
      generalizing L₁ L₂,
    { subst_vars, cases eq₂, constructor },
    { subst_vars,
      cases p with a b,
      rw [step.cons_left_iff] at h₁₂,
      rcases h₁₂ with ⟨L, h₁₂, rfl⟩ | rfl,
      { exact (ih rfl rfl).head h₁₂ },
      { exact (cons_cons h).tail step.cons_bnot_rev } }
  end
  cons_cons

lemma append_append_left_iff : ∀L, red (L ++ L₁) (L ++ L₂) ↔ red L₁ L₂
| []       := iff.rfl
| (p :: L) := by simp [append_append_left_iff L, cons_cons_iff]

lemma append_append (h₁ : red L₁ L₃) (h₂ : red L₂ L₄) : red (L₁ ++ L₂) (L₃ ++ L₄) :=
(refl_trans_gen_lift (λL, L ++ L₂) (assume a b, step.append_right) h₁).trans
  ((append_append_left_iff _).2 h₂)

lemma to_append_iff : red L (L₁ ++ L₂) ↔ (∃L₃ L₄, L = L₃ ++ L₄ ∧ red L₃ L₁ ∧ red L₄ L₂) :=
iff.intro
  begin
    generalize eq : L₁ ++ L₂ = L₁₂,
    assume h,
    induction h with L' L₁₂ hLL' h ih generalizing L₁ L₂,
    { exact ⟨_, _, eq.symm, by refl, by refl⟩ },
    { cases h with s e a b,
      rcases list.append_eq_append_iff.1 eq with ⟨s', rfl, rfl⟩ | ⟨e', rfl, rfl⟩,
      { have : L₁ ++ (s' ++ ((a, b) :: (a, bnot b) :: e)) =
                 (L₁ ++ s') ++ ((a, b) :: (a, bnot b) :: e),
        { simp },
        rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩,
        exact ⟨w₁, w₂, rfl, h₁, h₂.tail step.bnot⟩ },
      { have : (s ++ ((a, b) :: (a, bnot b) :: e')) ++ L₂ =
                 s ++ ((a, b) :: (a, bnot b) :: (e' ++ L₂)),
        { simp },
        rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩,
        exact ⟨w₁, w₂, rfl, h₁.tail step.bnot, h₂⟩ }, }
  end
  (assume ⟨L₃, L₄, eq, h₃, h₄⟩, eq.symm ▸ append_append h₃ h₄)

/-- The empty word `[]` only reduces to itself. -/
theorem nil_iff : red [] L ↔ L = [] :=
refl_trans_gen_iff_eq (assume l, red.not_step_nil)

/-- A letter only reduces to itself. -/
theorem singleton_iff {x} : red [x] L₁ ↔ L₁ = [x] :=
refl_trans_gen_iff_eq (assume l, not_step_singleton)

/-- If `x` is a letter and `w` is a word such that `xw` reduces to the empty word, then `w` reduces
to `x⁻¹` -/
theorem cons_nil_iff_singleton {x b} : red ((x, b) :: L) [] ↔ red L [(x, bnot b)] :=
iff.intro
  (assume h,
    have h₁ : red ((x, bnot b) :: (x, b) :: L) [(x, bnot b)], from cons_cons h,
    have h₂ : red ((x, bnot b) :: (x, b) :: L) L, from refl_trans_gen.single step.cons_bnot_rev,
    let ⟨L', h₁, h₂⟩ := church_rosser h₁ h₂ in
    by rw [singleton_iff] at h₁; subst L'; assumption)
  (assume h, (cons_cons h).tail step.cons_bnot)

theorem red_iff_irreducible {x1 b1 x2 b2} (h : (x1, b1) ≠ (x2, b2)) :
  red [(x1, bnot b1), (x2, b2)] L ↔ L = [(x1, bnot b1), (x2, b2)] :=
begin
  apply refl_trans_gen_iff_eq,
  generalize eq : [(x1, bnot b1), (x2, b2)] = L',
  assume L h',
  cases h',
  simp [list.cons_eq_append_iff, list.nil_eq_append_iff] at eq,
  rcases eq with ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩, subst_vars,
  simp at h,
  contradiction
end

/-- If `x` and `y` are distinct letters and `w₁ w₂` are words such that `xw₁` reduces to `yw₂`, then
`w₁` reduces to `x⁻¹yw₂`. -/
theorem inv_of_red_of_ne {x1 b1 x2 b2}
  (H1 : (x1, b1) ≠ (x2, b2))
  (H2 : red ((x1, b1) :: L₁) ((x2, b2) :: L₂)) :
  red L₁ ((x1, bnot b1) :: (x2, b2) :: L₂) :=
begin
  have : red ((x1, b1) :: L₁) ([(x2, b2)] ++ L₂), from H2,
  rcases to_append_iff.1 this with ⟨_ | ⟨p, L₃⟩, L₄, eq, h₁, h₂⟩,
  { simp [nil_iff] at h₁, contradiction },
  { cases eq,
    show red (L₃ ++ L₄) ([(x1, bnot b1), (x2, b2)] ++ L₂),
    apply append_append _ h₂,
    have h₁ : red ((x1, bnot b1) :: (x1, b1) :: L₃) [(x1, bnot b1), (x2, b2)],
    { exact cons_cons h₁ },
    have h₂ : red ((x1, bnot b1) :: (x1, b1) :: L₃) L₃,
    { exact step.cons_bnot_rev.to_red },
    rcases church_rosser h₁ h₂ with ⟨L', h₁, h₂⟩,
    rw [red_iff_irreducible H1] at h₁,
    rwa [h₁] at h₂ }
end

theorem step.sublist (H : red.step L₁ L₂) : L₂ <+ L₁ :=
by cases H; simp; constructor; constructor; refl

/-- If `w₁ w₂` are words such that `w₁` reduces to `w₂`, then `w₂` is a sublist of `w₁`. -/
theorem sublist : red L₁ L₂ → L₂ <+ L₁ :=
refl_trans_gen_of_transitive_reflexive
  (λl, list.sublist.refl l) (λa b c hab hbc, list.sublist.trans hbc hab) (λa b, red.step.sublist)

theorem sizeof_of_step : ∀ {L₁ L₂ : list (α × bool)}, step L₁ L₂ → L₂.sizeof < L₁.sizeof
| _ _ (@step.bnot _ L1 L2 x b) :=
  begin
    induction L1 with hd tl ih,
    case list.nil
    { dsimp [list.sizeof],
      have H : 1 + sizeof (x, b) + (1 + sizeof (x, bnot b) + list.sizeof L2)
        = (list.sizeof L2 + 1) + (sizeof (x, b) + sizeof (x, bnot b) + 1),
      { ac_refl },
      rw H,
      exact nat.le_add_right _ _ },
    case list.cons
    { dsimp [list.sizeof],
      exact nat.add_lt_add_left ih _ }
  end

theorem length (h : red L₁ L₂) : ∃ n, L₁.length = L₂.length + 2 * n :=
begin
  induction h with L₂ L₃ h₁₂ h₂₃ ih,
  { exact ⟨0, rfl⟩ },
  { rcases ih with ⟨n, eq⟩,
    existsi (1 + n),
    simp [mul_add, eq, (step.length h₂₃).symm, add_assoc] }
end

theorem antisymm (h₁₂ : red L₁ L₂) : red L₂ L₁ → L₁ = L₂ :=
match L₁, h₁₂.cases_head with
| _,  or.inl rfl            := assume h, rfl
| L₁, or.inr ⟨L₃, h₁₃, h₃₂⟩ := assume h₂₁,
  let ⟨n, eq⟩ := length (h₃₂.trans h₂₁) in
  have list.length L₃ + 0 = list.length L₃ + (2 * n + 2),
    by simpa [(step.length h₁₃).symm, add_comm, add_assoc] using eq,
  (nat.no_confusion $ nat.add_left_cancel this)
end

end red

theorem equivalence_join_red : equivalence (join (@red α)) :=
equivalence_join_refl_trans_gen $ assume a b c hab hac,
(match b, c, red.step.diamond hab hac rfl with
| b, _, or.inl rfl           := ⟨b, by refl, by refl⟩
| b, c, or.inr ⟨d, hbd, hcd⟩ := ⟨d, refl_gen.single hbd, refl_trans_gen.single hcd⟩
end)

theorem join_red_of_step (h : red.step L₁ L₂) : join red L₁ L₂ :=
join_of_single reflexive_refl_trans_gen h.to_red

theorem eqv_gen_step_iff_join_red : eqv_gen red.step L₁ L₂ ↔ join red L₁ L₂ :=
iff.intro
  (assume h,
    have eqv_gen (join red) L₁ L₂ := eqv_gen_mono (assume a b, join_red_of_step) h,
    (eqv_gen_iff_of_equivalence $ equivalence_join_red).1 this)
  (join_of_equivalence (eqv_gen.is_equivalence _) $ assume a b,
    refl_trans_gen_of_equivalence (eqv_gen.is_equivalence _) eqv_gen.rel)

end free_group

/-- The free group over a type, i.e. the words formed by the elements of the type and their formal
inverses, quotient by one step reduction. -/
def free_group (α : Type u) : Type u :=
quot $ @free_group.red.step α

namespace free_group

variables {α} {L L₁ L₂ L₃ L₄ : list (α × bool)}

/-- The canonical map from `list (α × bool)` to the free group on `α`. -/
def mk (L) : free_group α := quot.mk red.step L

@[simp] lemma quot_mk_eq_mk : quot.mk red.step L = mk L := rfl

@[simp] lemma quot_lift_mk (β : Type v) (f : list (α × bool) → β)
  (H : ∀ L₁ L₂, red.step L₁ L₂ → f L₁ = f L₂) :
quot.lift f H (mk L) = f L := rfl

@[simp] lemma quot_lift_on_mk (β : Type v) (f : list (α × bool) → β)
  (H : ∀ L₁ L₂, red.step L₁ L₂ → f L₁ = f L₂) :
quot.lift_on (mk L) f H = f L := rfl

instance : has_one (free_group α) := ⟨mk []⟩
lemma one_eq_mk : (1 : free_group α) = mk [] := rfl

instance : inhabited (free_group α) := ⟨1⟩

instance : has_mul (free_group α) :=
⟨λ x y, quot.lift_on x
    (λ L₁, quot.lift_on y (λ L₂, mk $ L₁ ++ L₂) (λ L₂ L₃ H, quot.sound $ red.step.append_left H))
    (λ L₁ L₂ H, quot.induction_on y $ λ L₃, quot.sound $ red.step.append_right H)⟩
@[simp] lemma mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂) := rfl

instance : has_inv (free_group α) :=
⟨λx, quot.lift_on x (λ L, mk (L.map $ λ x : α × bool, (x.1, bnot x.2)).reverse)
  (assume a b h, quot.sound $ by cases h; simp)⟩
@[simp] lemma inv_mk : (mk L)⁻¹ = mk (L.map $ λ x : α × bool, (x.1, bnot x.2)).reverse := rfl

instance : group (free_group α) :=
{ mul := (*),
  one := 1,
  inv := has_inv.inv,
  mul_assoc := by rintros ⟨L₁⟩ ⟨L₂⟩ ⟨L₃⟩; simp,
  one_mul := by rintros ⟨L⟩; refl,
  mul_one := by rintros ⟨L⟩; simp [one_eq_mk],
  mul_left_inv := by rintros ⟨L⟩; exact (list.rec_on L rfl $
    λ ⟨x, b⟩ tl ih, eq.trans (quot.sound $ by simp [one_eq_mk]) ih) }

/-- `of` is the canonical injection from the type to the free group over that type by sending each
element to the equivalence class of the letter that is the element. -/
def of (x : α) : free_group α :=
mk [(x, tt)]

theorem red.exact : mk L₁ = mk L₂ ↔ join red L₁ L₂ :=
calc (mk L₁ = mk L₂) ↔ eqv_gen red.step L₁ L₂ : iff.intro (quot.exact _) quot.eqv_gen_sound
  ... ↔ join red L₁ L₂ : eqv_gen_step_iff_join_red

/-- The canonical injection from the type to the free group is an injection. -/
theorem of_injective : function.injective (@of α) :=
λ _ _ H, let ⟨L₁, hx, hy⟩ := red.exact.1 H in
  by simp [red.singleton_iff] at hx hy; cc

section lift

variables {β : Type v} [group β] (f : α → β) {x y : free_group α}

/-- Given `f : α → β` with `β` a group, the canonical map `list (α × bool) → β` -/
def lift.aux : list (α × bool) → β :=
λ L, list.prod $ L.map $ λ x, cond x.2 (f x.1) (f x.1)⁻¹

theorem red.step.lift {f : α → β} (H : red.step L₁ L₂) :
  lift.aux f L₁ = lift.aux f L₂ :=
by cases H with _ _ _ b; cases b; simp [lift.aux]


/-- If `β` is a group, then any function from `α` to `β`
extends uniquely to a group homomorphism from
the free group over `α` to `β` -/
@[simps symm_apply]
def lift : (α → β) ≃ (free_group α →* β) :=
{ to_fun := λ f,
    monoid_hom.mk' (quot.lift (lift.aux f) $ λ L₁ L₂, red.step.lift) $ begin
      rintros ⟨L₁⟩ ⟨L₂⟩, simp [lift.aux],
    end,
  inv_fun := λ g, g ∘ of,
  left_inv := λ f, one_mul _,
  right_inv := λ g, monoid_hom.ext $ begin
    rintros ⟨L⟩,
    apply list.rec_on L,
    { exact g.map_one.symm, },
    { rintros ⟨x, _ | _⟩ t (ih : _ = g (mk t)),
      { show _ = g ((of x)⁻¹ * mk t),
        simpa [lift.aux] using ih },
      { show _ = g (of x * mk t),
        simpa [lift.aux] using ih }, },
  end }
variable {f}

@[simp] lemma lift.mk : lift f (mk L) =
  list.prod (L.map $ λ x, cond x.2 (f x.1) (f x.1)⁻¹) :=
rfl

@[simp] lemma lift.of {x} : lift f (of x) = f x :=
one_mul _

theorem lift.unique (g : free_group α →* β)
  (hg : ∀ x, g (of x) = f x) : ∀{x}, g x = lift f x :=
monoid_hom.congr_fun $ (lift.symm_apply_eq).mp (funext hg : g ∘ of = f)

/-- Two homomorphisms out of a free group are equal if they are equal on generators.

See note [partially-applied ext lemmas]. -/
@[ext]
lemma ext_hom {G : Type*} [group G] (f g : free_group α →* G) (h : ∀ a, f (of a) = g (of a)) :
  f = g :=
lift.symm.injective $ funext h

theorem lift.of_eq (x : free_group α) : lift of x = x :=
monoid_hom.congr_fun (lift.apply_symm_apply (monoid_hom.id _)) x

theorem lift.range_subset {s : subgroup β} (H : set.range f ⊆ s) :
  set.range (lift f) ⊆ s :=
by rintros _ ⟨⟨L⟩, rfl⟩; exact list.rec_on L s.one_mem
(λ ⟨x, b⟩ tl ih, bool.rec_on b
    (by simp at ih ⊢; from s.mul_mem
      (s.inv_mem $ H ⟨x, rfl⟩) ih)
    (by simp at ih ⊢; from s.mul_mem (H ⟨x, rfl⟩) ih))

theorem closure_subset {G : Type*} [group G] {s : set G} {t : subgroup G}
  (h : s ⊆ t) : subgroup.closure s ≤ t :=
begin
  simp only [h, subgroup.closure_le],
end

theorem lift.range_eq_closure :
  set.range (lift f) = subgroup.closure (set.range f) :=
set.subset.antisymm
  (lift.range_subset subgroup.subset_closure)
  begin
    suffices : (subgroup.closure (set.range f)) ≤ monoid_hom.range (lift f),
      simpa,
    rw subgroup.closure_le,
    rintros y ⟨x, hx⟩,
    exact ⟨of x, by simpa⟩
  end

end lift

section map

variables {β : Type v} (f : α → β) {x y : free_group α}

/-- Given `f : α → β`, the canonical map `list (α × bool) → list (β × bool)`. -/
def map.aux (L : list (α × bool)) : list (β × bool) :=
L.map $ λ x, (f x.1, x.2)

/-- Any function from `α` to `β` extends uniquely
to a group homomorphism from the free group
over `α` to the free group over `β`. Note that this is the bare function;
for the group homomorphism use `map`. -/
def map.to_fun (x : free_group α) : free_group β :=
x.lift_on (λ L, mk $ map.aux f L) $
λ L₁ L₂ H, quot.sound $ by cases H; simp [map.aux]

/-- Any function from `α` to `β` extends uniquely
to a group homomorphism from the free group
ver `α` to the free group over `β`. -/
def map : free_group α →* free_group β := monoid_hom.mk' (map.to_fun f)
begin
  rintros ⟨L₁⟩ ⟨L₂⟩,
  simp [map.to_fun, map.aux]
end

--by rintros ⟨L₁⟩ ⟨L₂⟩; simp [map, map.aux]

variable {f}

@[simp] lemma map.mk : map f (mk L) = mk (L.map (λ x, (f x.1, x.2))) :=
rfl

@[simp] lemma map.id : map id x = x :=
have H1 : (λ (x : α × bool), x) = id := rfl,
by rcases x with ⟨L⟩; simp [H1]

@[simp] lemma map.id' : map (λ z, z) x = x := map.id

theorem map.comp {γ : Type w} {f : α → β} {g : β → γ} {x} :
  map g (map f x) = map (g ∘ f) x :=
by rcases x with ⟨L⟩; simp

@[simp] lemma map.of {x} : map f (of x) = of (f x) := rfl

theorem map.unique (g : free_group α →* free_group β)
  (hg : ∀ x, g (of x) = of (f x)) : ∀{x}, g x = map f x :=
by rintros ⟨L⟩; exact list.rec_on L g.map_one
(λ ⟨x, b⟩ t (ih : g (mk t) = map f (mk t)), bool.rec_on b
  (show g ((of x)⁻¹ * mk t) = map f ((of x)⁻¹ * mk t),
     by simp [g.map_mul, g.map_inv, hg, ih])
  (show g (of x * mk t) = map f (of x * mk t),
     by simp [g.map_mul, hg, ih]))

/-- Equivalent types give rise to equivalent free groups. -/
def free_group_congr {α β} (e : α ≃ β) : free_group α ≃ free_group β :=
⟨map e, map e.symm,
 λ x, by simp [function.comp, map.comp],
 λ x, by simp [function.comp, map.comp]⟩

theorem map_eq_lift : map f x = lift (of ∘ f) x :=
eq.symm $ map.unique _ $ λ x, by simp

end map

section prod

variables [group α] (x y : free_group α)

/-- If `α` is a group, then any function from `α` to `α`
extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the multiplicative
version of `sum`. -/
def prod : free_group α →* α := lift id

variables {x y}

@[simp] lemma prod_mk :
  prod (mk L) = list.prod (L.map $ λ x, cond x.2 x.1 x.1⁻¹) :=
rfl

@[simp] lemma prod.of {x : α} : prod (of x) = x :=
lift.of

lemma prod.unique (g : free_group α →* α)
  (hg : ∀ x, g (of x) = x) {x} :
  g x = prod x :=
lift.unique g hg

end prod

theorem lift_eq_prod_map {β : Type v} [group β] {f : α → β} {x} :
  lift f x = prod (map f x) :=
begin
  rw ←lift.unique (prod.comp (map f)),
  { refl },
  { simp }
end

section sum

variables [add_group α] (x y : free_group α)

/-- If `α` is a group, then any function from `α` to `α`
extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the additive
version of `prod`. -/
def sum : α :=
@prod (multiplicative _) _ x

variables {x y}

@[simp] lemma sum_mk :
  sum (mk L) = list.sum (L.map $ λ x, cond x.2 x.1 (-x.1)) :=
rfl

@[simp] lemma sum.of {x : α} : sum (of x) = x :=
prod.of

-- note: there are no bundled homs with different notation in the domain and codomain, so we copy
-- these manually
@[simp] lemma sum.map_mul : sum (x * y) = sum x + sum y :=
(@prod (multiplicative _) _).map_mul _ _

@[simp] lemma sum.map_one : sum (1:free_group α) = 0 :=
(@prod (multiplicative _) _).map_one

@[simp] lemma sum.map_inv : sum x⁻¹ = -sum x :=
(@prod (multiplicative _) _).map_inv _

end sum

/-- The bijection between the free group on the empty type, and a type with one element. -/
def free_group_empty_equiv_unit : free_group empty ≃ unit :=
{ to_fun    := λ _, (),
  inv_fun   := λ _, 1,
  left_inv  := by rintros ⟨_ | ⟨⟨⟨⟩, _⟩, _⟩⟩; refl,
  right_inv := λ ⟨⟩, rfl }

/-- The bijection between the free group on a singleton, and the integers. -/
def free_group_unit_equiv_int : free_group unit ≃ ℤ :=
{ to_fun    := λ x,
   sum begin revert x, apply monoid_hom.to_fun,
    apply map (λ _, (1 : ℤ)),
  end,
  inv_fun   := λ x, of () ^ x,
  left_inv  :=
  begin
    rintros ⟨L⟩,
    refine list.rec_on L rfl _,
    exact (λ ⟨⟨⟩, b⟩ tl ih, by cases b; simp [gpow_add] at ih ⊢; rw ih; refl),
  end,
  right_inv :=
    λ x, int.induction_on x (by simp)
    (λ i ih, by simp at ih; simp [gpow_add, ih])
    (λ i ih, by simp at ih; simp [gpow_add, ih, sub_eq_add_neg, -int.add_neg_one])
}

section category

variables {β : Type u}

instance : monad free_group.{u} :=
{ pure := λ α, of,
  map := λ α β f, (map f),
  bind := λ α β x f, lift f x }

@[elab_as_eliminator]
protected theorem induction_on
  {C : free_group α → Prop}
  (z : free_group α)
  (C1 : C 1)
  (Cp : ∀ x, C $ pure x)
  (Ci : ∀ x, C (pure x) → C (pure x)⁻¹)
  (Cm : ∀ x y, C x → C y → C (x * y)) : C z :=
quot.induction_on z $ λ L, list.rec_on L C1 $ λ ⟨x, b⟩ tl ih,
bool.rec_on b (Cm _ _ (Ci _ $ Cp x) ih) (Cm _ _ (Cp x) ih)

@[simp] lemma map_pure (f : α → β) (x : α) : f <$> (pure x : free_group α) = pure (f x) :=
map.of

@[simp] lemma map_one (f : α → β) : f <$> (1 : free_group α) = 1 :=
(map f).map_one

@[simp] lemma map_mul (f : α → β) (x y : free_group α) : f <$> (x * y) = f <$> x * f <$> y :=
(map f).map_mul x y

@[simp] lemma map_inv (f : α → β) (x : free_group α) : f <$> (x⁻¹) = (f <$> x)⁻¹ :=
(map f).map_inv x

@[simp] lemma pure_bind (f : α → free_group β) (x) : pure x >>= f = f x :=
lift.of

@[simp] lemma one_bind (f : α → free_group β) : 1 >>= f = 1 :=
(lift f).map_one

@[simp] lemma mul_bind (f : α → free_group β) (x y : free_group α) :
  x * y >>= f = (x >>= f) * (y >>= f) :=
(lift f).map_mul _ _

@[simp] lemma inv_bind (f : α → free_group β) (x : free_group α) : x⁻¹ >>= f = (x >>= f)⁻¹ :=
(lift f).map_inv _

instance : is_lawful_monad free_group.{u} :=
{ id_map := λ α x, free_group.induction_on x (map_one id) (λ x, map_pure id x)
    (λ x ih, by rw [map_inv, ih]) (λ x y ihx ihy, by rw [map_mul, ihx, ihy]),
  pure_bind := λ α β x f, pure_bind f x,
  bind_assoc := λ α β γ x f g, free_group.induction_on x
    (by iterate 3 { rw one_bind }) (λ x, by iterate 2 { rw pure_bind })
    (λ x ih, by iterate 3 { rw inv_bind }; rw ih)
    (λ x y ihx ihy, by iterate 3 { rw mul_bind }; rw [ihx, ihy]),
  bind_pure_comp_eq_map := λ α β f x, free_group.induction_on x
    (by rw [one_bind, map_one]) (λ x, by rw [pure_bind, map_pure])
    (λ x ih, by rw [inv_bind, map_inv, ih]) (λ x y ihx ihy, by rw [mul_bind, map_mul, ihx, ihy]) }

end category

section reduce

variable [decidable_eq α]

/-- The maximal reduction of a word. It is computable
iff `α` has decidable equality. -/
def reduce (L : list (α × bool)) : list (α × bool) :=
list.rec_on L [] $ λ hd1 tl1 ih,
list.cases_on ih [hd1] $ λ hd2 tl2,
if hd1.1 = hd2.1 ∧ hd1.2 = bnot hd2.2 then tl2
else hd1 :: hd2 :: tl2

@[simp] lemma reduce.cons (x) : reduce (x :: L) =
  list.cases_on (reduce L) [x] (λ hd tl,
  if x.1 = hd.1 ∧ x.2 = bnot hd.2 then tl
  else x :: hd :: tl) := rfl

/-- The first theorem that characterises the function
`reduce`: a word reduces to its maximal reduction. -/
theorem reduce.red : red L (reduce L) :=
begin
  induction L with hd1 tl1 ih,
  case list.nil
  { constructor },
  case list.cons
  { dsimp,
    revert ih,
    generalize htl : reduce tl1 = TL,
    intro ih,
    cases TL with hd2 tl2,
    case list.nil
    { exact red.cons_cons ih },
    case list.cons
    { dsimp,
      by_cases h : hd1.fst = hd2.fst ∧ hd1.snd = bnot (hd2.snd),
      { rw [if_pos h],
        transitivity,
        { exact red.cons_cons ih },
        { cases hd1, cases hd2, cases h,
          dsimp at *, subst_vars,
          exact red.step.cons_bnot_rev.to_red } },
      { rw [if_neg h],
        exact red.cons_cons ih } } }
end

theorem reduce.not {p : Prop} :
  ∀ {L₁ L₂ L₃ : list (α × bool)} {x b}, reduce L₁ = L₂ ++ (x, b) :: (x, bnot b) :: L₃ → p
| [] L2 L3 _ _ := λ h, by cases L2; injections
| ((x,b)::L1) L2 L3 x' b' := begin
  dsimp,
  cases r : reduce L1,
  { dsimp, intro h,
    have := congr_arg list.length h,
    simp [-add_comm] at this,
    exact absurd this dec_trivial },
  cases hd with y c,
  by_cases x = y ∧ b = bnot c; simp [h]; intro H,
  { rw H at r,
    exact @reduce.not L1 ((y,c)::L2) L3 x' b' r },
  rcases L2 with _|⟨a, L2⟩,
  { injections, subst_vars,
    simp at h, cc },
  { refine @reduce.not L1 L2 L3 x' b' _,
    injection H with _ H,
    rw [r, H], refl }
end

/-- The second theorem that characterises the
function `reduce`: the maximal reduction of a word
only reduces to itself. -/
theorem reduce.min (H : red (reduce L₁) L₂) : reduce L₁ = L₂ :=
begin
  induction H with L1 L' L2 H1 H2 ih,
  { refl },
  { cases H1 with L4 L5 x b,
    exact reduce.not H2 }
end

/-- `reduce` is idempotent, i.e. the maximal reduction
of the maximal reduction of a word is the maximal
reduction of the word. -/
theorem reduce.idem : reduce (reduce L) = reduce L :=
eq.symm $ reduce.min reduce.red

theorem reduce.step.eq (H : red.step L₁ L₂) : reduce L₁ = reduce L₂ :=
let ⟨L₃, HR13, HR23⟩ := red.church_rosser reduce.red (reduce.red.head H) in
(reduce.min HR13).trans (reduce.min HR23).symm

/-- If a word reduces to another word, then they have
a common maximal reduction. -/
theorem reduce.eq_of_red (H : red L₁ L₂) : reduce L₁ = reduce L₂ :=
let ⟨L₃, HR13, HR23⟩ := red.church_rosser reduce.red (red.trans H reduce.red) in
(reduce.min HR13).trans (reduce.min HR23).symm

/-- If two words correspond to the same element in
the free group, then they have a common maximal
reduction. This is the proof that the function that
sends an element of the free group to its maximal
reduction is well-defined. -/
theorem reduce.sound (H : mk L₁ = mk L₂) : reduce L₁ = reduce L₂ :=
let ⟨L₃, H13, H23⟩ := red.exact.1 H in
(reduce.eq_of_red H13).trans (reduce.eq_of_red H23).symm

/-- If two words have a common maximal reduction,
then they correspond to the same element in the free group. -/
theorem reduce.exact (H : reduce L₁ = reduce L₂) : mk L₁ = mk L₂ :=
red.exact.2 ⟨reduce L₂, H ▸ reduce.red, reduce.red⟩

/-- A word and its maximal reduction correspond to
the same element of the free group. -/
theorem reduce.self : mk (reduce L) = mk L :=
reduce.exact reduce.idem

/-- If words `w₁ w₂` are such that `w₁` reduces to `w₂`,
then `w₂` reduces to the maximal reduction of `w₁`. -/
theorem reduce.rev (H : red L₁ L₂) : red L₂ (reduce L₁) :=
(reduce.eq_of_red H).symm ▸ reduce.red

/-- The function that sends an element of the free
group to its maximal reduction. -/
def to_word : free_group α → list (α × bool) :=
quot.lift reduce $ λ L₁ L₂ H, reduce.step.eq H

lemma to_word.mk : ∀{x : free_group α}, mk (to_word x) = x :=
by rintros ⟨L⟩; exact reduce.self

lemma to_word.inj : ∀(x y : free_group α), to_word x = to_word y → x = y :=
by rintros ⟨L₁⟩ ⟨L₂⟩; exact reduce.exact

/-- Constructive Church-Rosser theorem (compare `church_rosser`). -/
def reduce.church_rosser (H12 : red L₁ L₂) (H13 : red L₁ L₃) :
  { L₄ // red L₂ L₄ ∧ red L₃ L₄ } :=
⟨reduce L₁, reduce.rev H12, reduce.rev H13⟩

instance : decidable_eq (free_group α) :=
function.injective.decidable_eq to_word.inj

instance red.decidable_rel : decidable_rel (@red α)
| [] []          := is_true red.refl
| [] (hd2::tl2)  := is_false $ λ H, list.no_confusion (red.nil_iff.1 H)
| ((x,b)::tl) [] := match red.decidable_rel tl [(x, bnot b)] with
  | is_true H  := is_true $ red.trans (red.cons_cons H) $
    (@red.step.bnot _ [] [] _ _).to_red
  | is_false H := is_false $ λ H2, H $ red.cons_nil_iff_singleton.1 H2
  end
| ((x1,b1)::tl1) ((x2,b2)::tl2) := if h : (x1, b1) = (x2, b2)
  then match red.decidable_rel tl1 tl2 with
    | is_true H  := is_true $ h ▸ red.cons_cons H
    | is_false H := is_false $ λ H2, H $ h ▸ (red.cons_cons_iff _).1 $ H2
    end
  else match red.decidable_rel tl1 ((x1,bnot b1)::(x2,b2)::tl2) with
    | is_true H  := is_true $ (red.cons_cons H).tail red.step.cons_bnot
    | is_false H := is_false $ λ H2, H $ red.inv_of_red_of_ne h H2
    end

/-- A list containing every word that `w₁` reduces to. -/
def red.enum (L₁ : list (α × bool)) : list (list (α × bool)) :=
list.filter (λ L₂, red L₁ L₂) (list.sublists L₁)

theorem red.enum.sound (H : L₂ ∈ red.enum L₁) : red L₁ L₂ :=
list.of_mem_filter H

theorem red.enum.complete (H : red L₁ L₂) : L₂ ∈ red.enum L₁ :=
list.mem_filter_of_mem (list.mem_sublists.2 $ red.sublist H) H

instance : fintype { L₂ // red L₁ L₂ } :=
fintype.subtype (list.to_finset $ red.enum L₁) $
λ L₂, ⟨λ H, red.enum.sound $ list.mem_to_finset.1 H,
  λ H, list.mem_to_finset.2 $ red.enum.complete H⟩

end reduce

end free_group
