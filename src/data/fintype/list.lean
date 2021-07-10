/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.fintype.basic
import data.list.perm

/-!

# Fintype instance for nodup lists

The subtype of `{l : list α // l.nodup}` over a `[fintype α]`
admits a `fintype` instance.

## Implementation details
To construct the `fintype` instance, a function lifting a `multiset α`
to the `finset (list α)` that can construct it is provided.
This function is applied to the `finset.powerset` of `finset.univ`.

In general, a `decidable_eq` instance is not necessary to define this function,
but a proof of `(list.permutations l).nodup` is required to avoid it,
which is a TODO.

-/

variables {α : Type*} [decidable_eq α]

open list

namespace multiset

/--
The `finset` of `l : list α` that, given `m : multiset α`, have the property `⟦l⟧ = m`.
-/
def lists : multiset α → finset (list α) :=
λ s, quotient.lift_on s (λ l, l.permutations.to_finset)
(λ l l' (h : l ~ l'),
  begin
    ext sl,
    simp only [mem_permutations, list.mem_to_finset],
    exact ⟨λ hs, hs.trans h, λ hs, hs.trans h.symm⟩
  end)

@[simp] lemma lists_coe (l : list α) :
  lists (l : multiset α) = l.permutations.to_finset := rfl

@[simp] lemma mem_lists_iff (s : multiset α) (l : list α) :
  l ∈ lists s ↔ s = ⟦l⟧ :=
begin
  induction s using quotient.induction_on,
  simpa using perm_comm
end

end multiset

instance fintype_nodup_list [fintype α] : fintype {l : list α // l.nodup} :=
fintype.subtype ((finset.univ : finset α).powerset.bUnion (λ s, s.val.lists)) (λ l,
  begin
    suffices : (∃ (a : finset α), a.val = ↑l) ↔ l.nodup,
    { simpa },
    split,
    { rintro ⟨s, hs⟩,
      simpa [←multiset.coe_nodup, ←hs] using s.nodup },
    { intro hl,
      refine ⟨⟨↑l, hl⟩, _⟩,
      simp }
  end)
