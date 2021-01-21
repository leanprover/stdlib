/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import deprecated.subgroup

universes u v

open group

variables {R : Type u} [ring R]

/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and and additive inverse. -/
class is_subring (S : set R) extends is_add_subgroup S, is_submonoid S : Prop.

/-- The ring structure on a subring coerced to a type. -/
local attribute [instance]
def subset.ring {S : set R} [is_subring S] : ring S :=
{ left_distrib := λ x y z, subtype.eq $ left_distrib x.1 y.1 z.1,
  right_distrib := λ x y z, subtype.eq $ right_distrib x.1 y.1 z.1,
  .. subtype.add_comm_group, .. subtype.monoid }

/-- The ring structure on a subring coerced to a type. -/
def subtype.ring {S : set R} [is_subring S] : ring (subtype S) := subset.ring

namespace ring_hom

instance is_subring_preimage {R : Type u} {S : Type v} [ring R] [ring S]
  (f : R →+* S) (s : set S) [is_subring s] : is_subring (f ⁻¹' s) := {}

instance is_subring_image {R : Type u} {S : Type v} [ring R] [ring S]
  (f : R →+* S) (s : set R) [is_subring s] : is_subring (f '' s) := {}

instance is_subring_set_range {R : Type u} {S : Type v} [ring R] [ring S]
  (f : R →+* S) : is_subring (set.range f) := {}

end ring_hom

/-- Restrict the codomain of a ring homomorphism to a subring that includes the range. -/
def ring_hom.cod_restrict {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S)
  (s : set S) [is_subring s] (h : ∀ x, f x ∈ s) :
  R →+* s :=
{ to_fun := λ x, ⟨f x, h x⟩,
  map_add' := λ x y, subtype.eq $ f.map_add x y,
  map_zero' := subtype.eq f.map_zero,
  map_mul' := λ x y, subtype.eq $ f.map_mul x y,
  map_one' := subtype.eq f.map_one }

/-- Coersion `S → R` as a ring homormorphism-/
def is_subring.subtype (S : set R) [is_subring S] : S →+* R :=
⟨coe, rfl, λ _ _, rfl, rfl, λ _ _, rfl⟩

@[simp] lemma is_subring.coe_subtype {S : set R} [is_subring S] :
  ⇑(is_subring.subtype S) = coe := rfl

variables {cR : Type u} [comm_ring cR]

/-- The commutative ring structure on a subring coerced to a type. -/
def subset.comm_ring {S : set cR} [is_subring S] : comm_ring S :=
{ mul_comm := λ x y, subtype.eq $ mul_comm x.1 y.1,
  .. subset.ring }

/-- The commutative ring structure on a subring coerced to a type. -/
def subtype.comm_ring {S : set cR} [is_subring S] : comm_ring (subtype S) := subset.comm_ring

/-- The integral domain structure on a subring of an integral domain coerced to a type. -/
def subring.domain {D : Type*} [integral_domain D] (S : set D) [is_subring S] :
  integral_domain S :=
{ exists_pair_ne := ⟨0, 1, mt subtype.ext_iff_val.1 zero_ne_one⟩,
  eq_zero_or_eq_zero_of_mul_eq_zero := λ ⟨x, hx⟩ ⟨y, hy⟩,
    by { simp only [subtype.ext_iff_val, subtype.coe_mk], exact eq_zero_or_eq_zero_of_mul_eq_zero },
  .. subset.comm_ring }

instance is_subring.inter (S₁ S₂ : set R) [is_subring S₁] [is_subring S₂] :
  is_subring (S₁ ∩ S₂) :=
{ }

instance is_subring.Inter {ι : Sort*} (S : ι → set R) [h : ∀ y : ι, is_subring (S y)] :
  is_subring (set.Inter S) :=
{ }

lemma is_subring_Union_of_directed {ι : Type*} [hι : nonempty ι]
  (s : ι → set R) [∀ i, is_subring (s i)]
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
  is_subring (⋃i, s i) :=
{ to_is_add_subgroup := is_add_subgroup_Union_of_directed s directed,
  to_is_submonoid := is_submonoid_Union_of_directed s directed }

namespace ring

def closure (s : set R) := add_group.closure (monoid.closure s)

variable {s : set R}

local attribute [reducible] closure

theorem exists_list_of_mem_closure {a : R} (h : a ∈ closure s) :
  (∃ L : list (list R), (∀ l ∈ L, ∀ x ∈ l, x ∈ s ∨ x = (-1:R)) ∧ (L.map list.prod).sum = a) :=
add_group.in_closure.rec_on h
  (λ x hx, match x, monoid.exists_list_of_mem_closure hx with
    | _, ⟨L, h1, rfl⟩ := ⟨[L], list.forall_mem_singleton.2 (λ r hr, or.inl (h1 r hr)), zero_add _⟩
    end)
  ⟨[], list.forall_mem_nil _, rfl⟩
  (λ b _ ih, match b, ih with
    | _, ⟨L1, h1, rfl⟩ := ⟨L1.map (list.cons (-1)),
      λ L2 h2, match L2, list.mem_map.1 h2 with
        | _, ⟨L3, h3, rfl⟩ := list.forall_mem_cons.2 ⟨or.inr rfl, h1 L3 h3⟩
        end,
      by simp only [list.map_map, (∘), list.prod_cons, neg_one_mul];
      exact list.rec_on L1 neg_zero.symm (λ hd tl ih,
        by rw [list.map_cons, list.sum_cons, ih, list.map_cons, list.sum_cons, neg_add])⟩
    end)
  (λ r1 r2 hr1 hr2 ih1 ih2, match r1, r2, ih1, ih2 with
    | _, _, ⟨L1, h1, rfl⟩, ⟨L2, h2, rfl⟩ := ⟨L1 ++ L2, list.forall_mem_append.2 ⟨h1, h2⟩,
      by rw [list.map_append, list.sum_append]⟩
    end)

@[elab_as_eliminator]
protected theorem in_closure.rec_on {C : R → Prop} {x : R} (hx : x ∈ closure s)
  (h1 : C 1) (hneg1 : C (-1)) (hs : ∀ z ∈ s, ∀ n, C n → C (z * n))
  (ha : ∀ {x y}, C x → C y → C (x + y)) : C x :=
begin
  have h0 : C 0 := add_neg_self (1:R) ▸ ha h1 hneg1,
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩, clear hx,
  induction L with hd tl ih, { exact h0 },
  rw list.forall_mem_cons at HL,
  suffices : C (list.prod hd),
  { rw [list.map_cons, list.sum_cons],
    exact ha this (ih HL.2) },
  replace HL := HL.1, clear ih tl,
  suffices : ∃ L : list R, (∀ x ∈ L, x ∈ s) ∧ (list.prod hd = list.prod L ∨ list.prod hd = -list.prod L),
  { rcases this with ⟨L, HL', HP | HP⟩,
    { rw HP, clear HP HL hd, induction L with hd tl ih, { exact h1 },
      rw list.forall_mem_cons at HL',
      rw list.prod_cons,
      exact hs _ HL'.1 _ (ih HL'.2) },
    rw HP, clear HP HL hd, induction L with hd tl ih, { exact hneg1 },
    rw [list.prod_cons, neg_mul_eq_mul_neg],
    rw list.forall_mem_cons at HL',
    exact hs _ HL'.1 _ (ih HL'.2) },
  induction hd with hd tl ih,
  { exact ⟨[], list.forall_mem_nil _, or.inl rfl⟩ },
  rw list.forall_mem_cons at HL,
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩; cases HL.1 with hhd hhd,
  { exact ⟨hd :: L, list.forall_mem_cons.2 ⟨hhd, HL'⟩, or.inl $
      by rw [list.prod_cons, list.prod_cons, HP]⟩ },
  { exact ⟨L, HL', or.inr $ by rw [list.prod_cons, hhd, neg_one_mul, HP]⟩ },
  { exact ⟨hd :: L, list.forall_mem_cons.2 ⟨hhd, HL'⟩, or.inr $
      by rw [list.prod_cons, list.prod_cons, HP, neg_mul_eq_mul_neg]⟩ },
  { exact ⟨L, HL', or.inl $ by rw [list.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩ }
end

instance : is_subring (closure s) :=
{ one_mem := add_group.mem_closure is_submonoid.one_mem,
  mul_mem := λ a b ha hb, add_group.in_closure.rec_on hb
    (λ b hb, add_group.in_closure.rec_on ha
      (λ a ha, add_group.subset_closure (is_submonoid.mul_mem ha hb))
      ((zero_mul b).symm ▸ is_add_submonoid.zero_mem)
      (λ a ha hab, (neg_mul_eq_neg_mul a b) ▸ is_add_subgroup.neg_mem hab)
      (λ a c ha hc hab hcb, (add_mul a c b).symm ▸ is_add_submonoid.add_mem hab hcb))
    ((mul_zero a).symm ▸ is_add_submonoid.zero_mem)
    (λ b hb hab, (neg_mul_eq_mul_neg a b) ▸ is_add_subgroup.neg_mem hab)
    (λ b c hb hc hab hac, (mul_add a b c).symm ▸ is_add_submonoid.add_mem hab hac),
  .. add_group.closure.is_add_subgroup _ }

theorem mem_closure {a : R} : a ∈ s → a ∈ closure s :=
add_group.mem_closure ∘ @monoid.subset_closure _ _ _ _

theorem subset_closure : s ⊆ closure s :=
λ _, mem_closure

theorem closure_subset {t : set R} [is_subring t] : s ⊆ t → closure s ⊆ t :=
add_group.closure_subset ∘ monoid.closure_subset

theorem closure_subset_iff (s t : set R) [is_subring t] : closure s ⊆ t ↔ s ⊆ t :=
(add_group.closure_subset_iff _ t).trans
  ⟨set.subset.trans monoid.subset_closure, monoid.closure_subset⟩

theorem closure_mono {s t : set R} (H : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans H subset_closure

lemma image_closure {S : Type*} [ring S] (f : R →+* S) (s : set R) :
  f '' closure s = closure (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { rw [f.map_one], apply is_submonoid.one_mem },
    { rw [f.map_neg, f.map_one],
      apply is_add_subgroup.neg_mem, apply is_submonoid.one_mem },
    { rw [f.map_mul],
      apply is_submonoid.mul_mem; solve_by_elim [subset_closure, set.mem_image_of_mem] },
    { rw [f.map_add], apply is_add_submonoid.add_mem, assumption' },
  end
  (closure_subset $ set.image_subset _ subset_closure)


end ring
