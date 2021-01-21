/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import data.fintype.basic

/-!
Type class for finitely enumerable types. The property is stronger
than `fintype` in that it assigns each element a rank in a finite
enumeration.
-/

open finset

/-- `fin_enum α` means that `α` is finite and can be enumerated in some order,
  i.e. `α` has an explicit bijection with `fin n` for some n. -/
class fin_enum (α : Sort*) :=
(card : ℕ)
(equiv [] : α ≃ fin card)
[dec_eq : decidable_eq α]

attribute [instance, priority 100] fin_enum.dec_eq

namespace fin_enum

variables {α : Type*}

/-- transport a `fin_enum` instance across an equivalence -/
def of_equiv (α) {β} [fin_enum α] (h : β ≃ α) : fin_enum β :=
{ card := card α,
  equiv := h.trans (equiv α),
  dec_eq := (h.trans (equiv _)).decidable_eq }

/-- create a `fin_enum` instance from an exhaustive list without duplicates -/
def of_nodup_list [decidable_eq α] (xs : list α) (h : ∀ x : α, x ∈ xs) (h' : list.nodup xs) :
  fin_enum α :=
{ card := xs.length,
  equiv := ⟨λ x, ⟨xs.index_of x,by rw [list.index_of_lt_length]; apply h⟩,
           λ ⟨i,h⟩, xs.nth_le _ h,
           λ x, by simp [of_nodup_list._match_1],
           λ ⟨i,h⟩, by simp [of_nodup_list._match_1,*]; rw list.nth_le_index_of;
             apply list.nodup_erase_dup ⟩ }

/-- create a `fin_enum` instance from an exhaustive list; duplicates are removed -/
def of_list [decidable_eq α] (xs : list α) (h : ∀ x : α, x ∈ xs) : fin_enum α :=
of_nodup_list xs.erase_dup (by simp *) (list.nodup_erase_dup _)

/-- create an exhaustive list of the values of a given type -/
def to_list (α) [fin_enum α] : list α :=
(list.fin_range (card α)).map (equiv α).symm

open function

@[simp] lemma mem_to_list [fin_enum α] (x : α) : x ∈ to_list α :=
by simp [to_list]; existsi equiv α x; simp

@[simp] lemma nodup_to_list [fin_enum α] : list.nodup (to_list α) :=
by simp [to_list]; apply list.nodup_map; [apply equiv.injective, apply list.nodup_fin_range]

/-- create a `fin_enum` instance using a surjection -/
def of_surjective {β} (f : β → α) [decidable_eq α] [fin_enum β] (h : surjective f) : fin_enum α :=
of_list ((to_list β).map f) (by intro; simp; exact h _)

/-- create a `fin_enum` instance using an injection -/
noncomputable def of_injective {α β} (f : α → β) [decidable_eq α] [fin_enum β] (h : injective f) :
  fin_enum α :=
of_list ((to_list β).filter_map (partial_inv f))
begin
  intro x,
  simp only [mem_to_list, true_and, list.mem_filter_map],
  use f x,
  simp only [h, function.partial_inv_left],
end

instance pempty : fin_enum pempty :=
of_list [] (λ x, pempty.elim x)

instance empty : fin_enum empty :=
of_list [] (λ x, empty.elim x)

instance punit : fin_enum punit :=
of_list [punit.star] (λ x, by cases x; simp)

instance prod {β} [fin_enum α] [fin_enum β] : fin_enum (α × β) :=
of_list ( (to_list α).product (to_list β) ) (λ x, by cases x; simp)

instance sum {β} [fin_enum α] [fin_enum β] : fin_enum (α ⊕ β) :=
of_list ( (to_list α).map sum.inl ++ (to_list β).map sum.inr ) (λ x, by cases x; simp)

instance fin {n} : fin_enum (fin n) :=
of_list (list.fin_range _) (by simp)

instance quotient.enum [fin_enum α] (s : setoid α)
  [decidable_rel ((≈) : α → α → Prop)] : fin_enum (quotient s) :=
fin_enum.of_surjective quotient.mk (λ x, quotient.induction_on x (λ x, ⟨x, rfl⟩))

/-- enumerate all finite sets of a given type -/
def finset.enum [decidable_eq α] : list α → list (finset α)
| [] := [∅]
| (x :: xs) :=
  do r ← finset.enum xs,
     [r,{x} ∪ r]

@[simp]lemma finset.mem_enum [decidable_eq α] (s : finset α) (xs : list α) :
  s ∈ finset.enum xs ↔ ∀ x ∈ s, x ∈ xs :=
begin
  induction xs generalizing s; simp [*,finset.enum],
  { simp [finset.eq_empty_iff_forall_not_mem,(∉)], refl },
  { split, rintro ⟨a,h,h'⟩ x hx,
    cases h',
    { right, apply h, subst a, exact hx, },
    { simp only [h', mem_union, mem_singleton] at hx ⊢, cases hx,
      { exact or.inl hx },
      { exact or.inr (h _ hx) }  },
    intro h, existsi s \ ({xs_hd} : finset α),
    simp only [and_imp, union_comm, mem_sdiff, mem_singleton],
    simp only [or_iff_not_imp_left] at h,
    existsi h,
    by_cases xs_hd ∈ s,
    { have : {xs_hd} ⊆ s, simp only [has_subset.subset, *, forall_eq, mem_singleton],
      simp only [union_sdiff_of_subset this, or_true, finset.union_sdiff_of_subset,
        eq_self_iff_true], },
    { left, symmetry, simp only [sdiff_eq_self],
      intro a, simp only [and_imp, mem_inter, mem_singleton, not_mem_empty],
      intros h₀ h₁, subst a, apply h h₀, } }
end

instance finset.fin_enum [fin_enum α] : fin_enum (finset α) :=
of_list (finset.enum (to_list α)) (by intro; simp)

instance subtype.fin_enum [fin_enum α] (p : α → Prop) [decidable_pred p] : fin_enum {x // p x} :=
of_list ((to_list α).filter_map $ λ x, if h : p x then some ⟨_,h⟩ else none)
  (by rintro ⟨x,h⟩; simp; existsi x; simp *)

instance (β : α → Type*)
  [fin_enum α] [∀ a, fin_enum (β a)] : fin_enum (sigma β) :=
of_list
  ((to_list α).bind $ λ a, (to_list (β a)).map $ sigma.mk a)
  (by intro x; cases x; simp)

instance psigma.fin_enum {β : α → Type*} [fin_enum α] [∀ a, fin_enum (β a)] :
  fin_enum (Σ' a, β a) :=
fin_enum.of_equiv _ (equiv.psigma_equiv_sigma _)

instance psigma.fin_enum_prop_left {α : Prop} {β : α → Type*} [∀ a, fin_enum (β a)] [decidable α] :
  fin_enum (Σ' a, β a) :=
if h : α then of_list ((to_list (β h)).map $ psigma.mk h) (λ ⟨a,Ba⟩, by simp)
else of_list [] (λ ⟨a,Ba⟩, (h a).elim)

instance psigma.fin_enum_prop_right {β : α → Prop} [fin_enum α] [∀ a, decidable (β a)] :
  fin_enum (Σ' a, β a) :=
fin_enum.of_equiv {a // β a} ⟨λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, rfl, λ ⟨x, y⟩, rfl⟩

instance psigma.fin_enum_prop_prop {α : Prop} {β : α → Prop} [decidable α] [∀ a, decidable (β a)] :
  fin_enum (Σ' a, β a) :=
if h : ∃ a, β a
  then of_list [⟨h.fst,h.snd⟩] (by rintro ⟨⟩; simp)
  else of_list [] (λ a, (h ⟨a.fst,a.snd⟩).elim)

@[priority 100]
instance [fin_enum α] : fintype α :=
{ elems := univ.map (equiv α).symm.to_embedding,
  complete := by intros; simp; existsi (equiv α x); simp }

/-- For `pi.cons x xs y f` create a function where every `i ∈ xs` is mapped to `f i` and
`x` is mapped to `y`  -/
def pi.cons {β : α → Type*} [decidable_eq α] (x : α) (xs : list α) (y : β x)
  (f : Π a, a ∈ xs → β a) :
  Π a, a ∈ (x :: xs : list α) → β a
| b h :=
  if h' : b = x then cast (by rw h') y
    else f b (list.mem_of_ne_of_mem h' h)

/-- Given `f` a function whose domain is `x :: xs`, produce a function whose domain
is restricted to `xs`.  -/
def pi.tail {α : Type*} {β : α → Type*} {x : α} {xs : list α}
  (f : Π a, a ∈ (x :: xs : list α) → β a) :
  Π a, a ∈ xs → β a
| a h := f a (list.mem_cons_of_mem _ h)

/-- `pi xs f` creates the list of functions `g` such that, for `x ∈ xs`, `g x ∈ f x` -/
def pi {α : Type*} {β : α → Type*} [decidable_eq α] : Π xs : list α, (Π a, list (β a)) →
  list (Π a, a ∈ xs → β a)
| [] fs := [λ x h, h.elim]
| (x :: xs) fs :=
  fin_enum.pi.cons x xs <$> fs x <*> pi xs fs

lemma mem_pi  {α : Type*} {β : α → Type*} [fin_enum α] [∀a, fin_enum (β a)] (xs : list α)
  (f : Π a, a ∈ xs → β a) :
  f ∈ pi xs (λ x, to_list (β x)) :=
begin
  induction xs; simp [pi,-list.map_eq_map] with monad_norm functor_norm,
  { ext a ⟨ ⟩ },
  { existsi pi.cons xs_hd xs_tl (f _ (list.mem_cons_self _ _)),
    split, exact ⟨_,rfl⟩,
    existsi pi.tail f, split,
    { apply xs_ih, },
    { ext x h, simp [pi.cons], split_ifs, subst x, refl, refl }, }
end

/-- enumerate all functions whose domain and range are finitely enumerable -/
def pi.enum  {α : Type*} (β : α → Type*) [fin_enum α] [∀a, fin_enum (β a)] : list (Π a, β a) :=
(pi (to_list α) (λ x, to_list (β x))).map (λ f x, f x (mem_to_list _))

lemma pi.mem_enum  {α : Type*} {β : α → Type*} [fin_enum α] [∀a, fin_enum (β a)] (f : Π a, β a) :
  f ∈ pi.enum β :=
by simp [pi.enum]; refine ⟨λ a h, f a, mem_pi _ _, rfl⟩

instance pi.fin_enum {α : Type*} {β : α → Type*}
  [fin_enum α] [∀a, fin_enum (β a)] : fin_enum (Πa, β a) :=
of_list (pi.enum _) (λ x, pi.mem_enum _)

instance pfun_fin_enum (p : Prop) [decidable p] (α : p → Type*)
  [Π hp, fin_enum (α hp)] : fin_enum (Π hp : p, α hp) :=
if hp : p then of_list ( (to_list (α hp)).map $ λ x hp', x ) (by intro; simp; exact ⟨x hp,rfl⟩)
          else of_list [λ hp', (hp hp').elim] (by intro; simp; ext hp'; cases hp hp')

end fin_enum
