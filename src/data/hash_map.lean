/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.pnat.basic
import data.list.range
import data.array.lemmas
import algebra.group

/-!
# Hash maps

Defines a hash map data structure, representing a finite key-value map
with a value type that may depend on the key type.  The structure
requires a `nat`-valued hash function to associate keys to buckets.

## Main definitions

* `hash_map`: constructed with `mk_hash_map`.

## Implementation details

A hash map with key type `α` and (dependent) value type `β : α → Type*`
consists of an array of *buckets*, which are lists containing
key/value pairs for that bucket.  The hash function is taken modulo `n`
to assign keys to their respective bucket.  Because of this, some care
should be put into the hash function to ensure it evenly distributes
keys.

The bucket array is an `array`.  These have special VM support for
in-place modification if there is only ever one reference to them.  If
one takes special care to never keep references to old versions of a
hash map alive after updating it, then the hash map will be modified
in-place.  In this documentation, when we say a hash map is modified
in-place, we are assuming the API is being used in this manner.

When inserting (`hash_map.insert`), if the number of stored pairs (the
*size*) is going to exceed the number of buckets, then a new hash map
is first created with double the number of buckets and everything in
the old hash map is reinserted along with the new key/value pair.
Otherwise, the bucket array is modified in-place.  The amortized
running time of inserting $$n$$ elements into a hash map is $$O(n)$$.

When removing (`hash_map.erase`), the hash map is modified in-place.
The implementation does not reduce the number of buckets in the hash
map if the size gets too low.

## Tags

hash map

-/

universes u v w

/-- `bucket_array α β` is the underlying data type for `hash_map α β`,
  an array of linked lists of key-value pairs. -/
def bucket_array (α : Type u) (β : α → Type v) (n : ℕ+) :=
array n (list Σ a, β a)

/-- Make a hash_map index from a `nat` hash value and a (positive) buffer size -/
def hash_map.mk_idx (n : ℕ+) (i : nat) : fin n :=
⟨i % n, nat.mod_lt _ n.2⟩

namespace bucket_array
section
parameters {α : Type u} {β : α → Type v} (hash_fn : α → nat)
variables {n : ℕ+} (data : bucket_array α β n)

instance : inhabited (bucket_array α β n) :=
⟨mk_array _ []⟩

/-- Read the bucket corresponding to an element -/
def read (a : α) : list Σ a, β a :=
let bidx := hash_map.mk_idx n (hash_fn a) in
data.read bidx

/-- Write the bucket corresponding to an element -/
def write (a : α) (l : list Σ a, β a) : bucket_array α β n :=
let bidx := hash_map.mk_idx n (hash_fn a) in
data.write bidx l

/-- Modify (read, apply `f`, and write) the bucket corresponding to an element -/
def modify (a : α) (f : list (Σ a, β a) → list (Σ a, β a)) : bucket_array α β n :=
let bidx := hash_map.mk_idx n (hash_fn a) in
array.write data bidx (f (array.read data bidx))

/-- The list of all key-value pairs in the bucket list -/
def as_list : list Σ a, β a := data.to_list.join

theorem mem_as_list {a : Σ a, β a} : a ∈ data.as_list ↔ ∃i, a ∈ array.read data i :=
have (∃ (l : list (Σ (a : α), β a)) (i : fin (n.val)), a ∈ l ∧ array.read data i = l) ↔
  ∃ (i : fin (n.val)), a ∈ array.read data i,
by rw exists_swap; exact exists_congr (λ i, by simp),
by simp [as_list]; simpa [array.mem.def, and_comm]

/-- Fold a function `f` over the key-value pairs in the bucket list -/
def foldl {δ : Type w} (d : δ) (f : δ → Π a, β a → δ) : δ :=
data.foldl d (λ b d, b.foldl (λ r a, f r a.1 a.2) d)

theorem foldl_eq {δ : Type w} (d : δ) (f : δ → Π a, β a → δ) :
  data.foldl d f = data.as_list.foldl (λ r a, f r a.1 a.2) d :=
by rw [foldl, as_list, list.foldl_join, ← array.to_list_foldl]

end
end bucket_array

namespace hash_map
section
parameters {α : Type u} {β : α → Type v} (hash_fn : α → nat)

/-- Insert the pair `⟨a, b⟩` into the correct location in the bucket array
  (without checking for duplication) -/
def reinsert_aux {n} (data : bucket_array α β n) (a : α) (b : β a) : bucket_array α β n :=
data.modify hash_fn a (λl, ⟨a, b⟩ :: l)

theorem mk_as_list (n : ℕ+) : bucket_array.as_list (mk_array n [] : bucket_array α β n) = [] :=
list.eq_nil_iff_forall_not_mem.mpr $ λ x m,
let ⟨i, h⟩ := (bucket_array.mem_as_list _).1 m in h

parameter [decidable_eq α]

/-- Search a bucket for a key `a` and return the value -/
def find_aux (a : α) : list (Σ a, β a) → option (β a)
| []          := none
| (⟨a',b⟩::t) := if h : a' = a then some (eq.rec_on h b) else find_aux t

theorem find_aux_iff {a : α} {b : β a} :
  Π {l : list Σ a, β a}, (l.map sigma.fst).nodup → (find_aux a l = some b ↔ sigma.mk a b ∈ l)
| []          nd := ⟨λn, by injection n, false.elim⟩
| (⟨a',b'⟩::t) nd := begin
  by_cases a' = a,
  { clear find_aux_iff, subst h,
    suffices : b' = b ↔ b' = b ∨ sigma.mk a' b ∈ t, {simpa [find_aux, eq_comm]},
    refine (or_iff_left_of_imp (λ m, _)).symm,
    have : a' ∉ t.map sigma.fst, from list.not_mem_of_nodup_cons nd,
    exact this.elim (list.mem_map_of_mem sigma.fst m) },
  { have : sigma.mk a b ≠ ⟨a', b'⟩,
    { intro e, injection e with e, exact h e.symm },
    simp at nd, simp [find_aux, h, ne.symm h, find_aux_iff, nd] }
end

/-- Returns `tt` if the bucket `l` contains the key `a` -/
def contains_aux (a : α) (l : list Σ a, β a) : bool :=
(find_aux a l).is_some

theorem contains_aux_iff {a : α} {l : list Σ a, β a} (nd : (l.map sigma.fst).nodup) :
  contains_aux a l ↔ a ∈ l.map sigma.fst :=
begin
  unfold contains_aux,
  cases h : find_aux a l with b; simp,
  { assume (b : β a) (m : sigma.mk a b ∈ l),
    rw (find_aux_iff nd).2 m at h,
    contradiction },
  { show ∃ (b : β a), sigma.mk a b ∈ l,
    exact ⟨_, (find_aux_iff nd).1 h⟩ },
end

/-- Modify a bucket to replace a value in the list. Leaves the list
 unchanged if the key is not found. -/
def replace_aux (a : α) (b : β a) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then ⟨a, b⟩::t else ⟨a', b'⟩ :: replace_aux t

/-- Modify a bucket to remove a key, if it exists. -/
def erase_aux (a : α) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then t else ⟨a', b'⟩ :: erase_aux t

/-- The predicate `valid bkts sz` means that `bkts` satisfies the `hash_map`
  invariants: There are exactly `sz` elements in it, every pair is in the
  bucket determined by its key and the hash function, and no key appears
  multiple times in the list. -/
structure valid {n} (bkts : bucket_array α β n) (sz : nat) : Prop :=
(len : bkts.as_list.length = sz)
(idx : ∀ {i} {a : Σ a, β a}, a ∈ array.read bkts i →
  mk_idx n (hash_fn a.1) = i)
(nodup : ∀i, ((array.read bkts i).map sigma.fst).nodup)

theorem valid.idx_enum {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz)
  {i l} (he : (i, l) ∈ bkts.to_list.enum) {a} {b : β a} (hl : sigma.mk a b ∈ l) :
  ∃ h, mk_idx n (hash_fn a) = ⟨i, h⟩ :=
(array.mem_to_list_enum.mp he).imp (λ h e, by subst e; exact v.idx hl)

theorem valid.idx_enum_1 {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz)
  {i l} (he : (i, l) ∈ bkts.to_list.enum) {a} {b : β a} (hl : sigma.mk a b ∈ l) :
  (mk_idx n (hash_fn a)).1 = i :=
let ⟨h, e⟩ := v.idx_enum _ he hl in by rw e; refl

theorem valid.as_list_nodup {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz) :
  (bkts.as_list.map sigma.fst).nodup :=
begin
  suffices : (bkts.to_list.map (list.map sigma.fst)).pairwise list.disjoint,
  { suffices : ∀ l, array.mem l bkts → (l.map sigma.fst).nodup,
      by simpa [bucket_array.as_list, list.nodup_join, *],
    rintros l ⟨i, rfl⟩,
    apply v.nodup },
  rw [← list.enum_map_snd bkts.to_list, list.pairwise_map, list.pairwise_map],
  have : (bkts.to_list.enum.map prod.fst).nodup := by simp [list.nodup_range],
  refine list.pairwise.imp_of_mem _ ((list.pairwise_map _).1 this),
  rw prod.forall, intros i l₁,
  rw prod.forall, intros j l₂ me₁ me₂ ij,
  simp [list.disjoint], intros a b ml₁ b' ml₂,
  apply ij, rwa [← v.idx_enum_1 _ me₁ ml₁, ← v.idx_enum_1 _ me₂ ml₂]
end

theorem mk_valid (n : ℕ+) : @valid n (mk_array n []) 0 :=
⟨by simp [mk_as_list], λ i a h, by cases h, λ i, list.nodup_nil⟩

theorem valid.find_aux_iff {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz) {a : α}
  {b : β a} :
  find_aux a (bkts.read hash_fn a) = some b ↔ sigma.mk a b ∈ bkts.as_list :=
(find_aux_iff (v.nodup _)).trans $
by rw bkts.mem_as_list; exact ⟨λ h, ⟨_, h⟩, λ ⟨i, h⟩, (v.idx h).symm ▸ h⟩

theorem valid.contains_aux_iff {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz)
  (a : α) :
  contains_aux a (bkts.read hash_fn a) ↔ a ∈ bkts.as_list.map sigma.fst :=
by simp [contains_aux, option.is_some_iff_exists, v.find_aux_iff hash_fn]

section
  parameters {n : ℕ+} {bkts : bucket_array α β n}
             {bidx : fin n} {f : list (Σ a, β a) → list (Σ a, β a)}
             (u v1 v2 w : list Σ a, β a)

  local notation `L` := array.read bkts bidx
  private def bkts' : bucket_array α β n := array.write bkts bidx (f L)

  variables (hl : L = u ++ v1 ++ w)
            (hfl : f L = u ++ v2 ++ w)
  include hl hfl

  theorem append_of_modify :
  ∃ u' w', bkts.as_list = u' ++ v1 ++ w' ∧ bkts'.as_list = u' ++ v2 ++ w' :=
  begin
    unfold bucket_array.as_list,
    have h : (bidx : ℕ) < bkts.to_list.length, { simp only [bidx.is_lt, array.to_list_length] },
    refine ⟨(bkts.to_list.take bidx).join ++ u, w ++ (bkts.to_list.drop (bidx+1)).join, _, _⟩,
    { conv { to_lhs,
        rw [← list.take_append_drop bidx bkts.to_list, list.drop_eq_nth_le_cons h],
        simp [hl] }, simp },
    { conv { to_lhs,
        rw [bkts', array.write_to_list, list.update_nth_eq_take_cons_drop _ h],
        simp [hfl] }, simp }
  end

  variables (hvnd : (v2.map sigma.fst).nodup)
            (hal : ∀ (a : Σ a, β a), a ∈ v2 → mk_idx n (hash_fn a.1) = bidx)
            (djuv : (u.map sigma.fst).disjoint (v2.map sigma.fst))
            (djwv : (w.map sigma.fst).disjoint (v2.map sigma.fst))
  include hvnd hal djuv djwv

  theorem valid.modify {sz : ℕ} (v : valid bkts sz) :
    v1.length ≤ sz + v2.length ∧ valid bkts' (sz + v2.length - v1.length) :=
  begin
    rcases append_of_modify u v1 v2 w hl hfl with ⟨u', w', e₁, e₂⟩,
    rw [← v.len, e₁],
    suffices : valid bkts' (u' ++ v2 ++ w').length,
    { simpa [ge, add_comm, add_left_comm, nat.le_add_right, nat.add_sub_cancel_left] },
    refine ⟨congr_arg _ e₂, λ i a, _, λ i, _⟩,
    { by_cases bidx = i,
      { subst i, rw [bkts', array.read_write, hfl],
        have := @valid.idx _ _ _ v bidx a,
        simp only [hl, list.mem_append, or_imp_distrib, forall_and_distrib] at this ⊢,
        exact ⟨⟨this.1.1, hal _⟩, this.2⟩ },
      { rw [bkts', array.read_write_of_ne _ _ h], apply v.idx } },
    { by_cases bidx = i,
      { subst i, rw [bkts', array.read_write, hfl],
        have := @valid.nodup _ _ _ v bidx,
        simp [hl, list.nodup_append] at this,
        simp [list.nodup_append, this, hvnd, djuv, djwv.symm] },
      { rw [bkts', array.read_write_of_ne _ _ h], apply v.nodup } }
  end
end

theorem valid.replace_aux (a : α) (b : β a) : Π (l : list (Σ a, β a)), a ∈ l.map sigma.fst →
  ∃ (u w : list Σ a, β a) b', l = u ++ [⟨a, b'⟩] ++ w ∧ replace_aux a b l = u ++ [⟨a, b⟩] ++ w
| []            := false.elim
| (⟨a', b'⟩::t) := begin
  by_cases e : a' = a,
  { subst a',
    suffices : ∃ (u w : list Σ a, β a) (b'' : β a),
      (sigma.mk a b') :: t = u ++ ⟨a, b''⟩ :: w ∧
      replace_aux a b (⟨a, b'⟩ :: t) = u ++ ⟨a, b⟩ :: w, {simpa},
    refine ⟨[], t, b', _⟩, simp [replace_aux] },
  { suffices : ∀ (x : β a) (_ : sigma.mk a x ∈ t), ∃ u w (b'' : β a),
      (sigma.mk a' b') :: t = u ++ ⟨a, b''⟩ :: w ∧
      (sigma.mk a' b') :: (replace_aux a b t) = u ++ ⟨a, b⟩ :: w,
    { simpa [replace_aux, ne.symm e, e] },
    intros x m,
    have IH : ∀ (x : β a) (_ : sigma.mk a x ∈ t), ∃ u w (b'' : β a),
      t = u ++ ⟨a, b''⟩ :: w ∧ replace_aux a b t = u ++ ⟨a, b⟩ :: w,
    { simpa using valid.replace_aux t },
    rcases IH x m with ⟨u, w, b'', hl, hfl⟩,
    exact ⟨⟨a', b'⟩ :: u, w, b'', by simp [hl, hfl.symm, ne.symm e]⟩ }
end

theorem valid.replace {n : ℕ+}
  {bkts : bucket_array α β n} {sz : ℕ} (a : α) (b : β a)
  (Hc : contains_aux a (bkts.read hash_fn a))
  (v : valid bkts sz) : valid (bkts.modify hash_fn a (replace_aux a b)) sz :=
begin
  have nd := v.nodup (mk_idx n (hash_fn a)),
  rcases hash_map.valid.replace_aux a b (array.read bkts (mk_idx n (hash_fn a)))
    ((contains_aux_iff nd).1 Hc) with ⟨u, w, b', hl, hfl⟩,
  simp [hl, list.nodup_append] at nd,
  refine (v.modify hash_fn
    u [⟨a, b'⟩] [⟨a, b⟩] w hl hfl (list.nodup_singleton _)
    (λa' e, by simp at e; rw e)
    (λa' e1 e2, _)
    (λa' e1 e2, _)).2;
  { revert e1, simp [-sigma.exists] at e2, subst a', simp [nd] }
end

theorem valid.insert {n : ℕ+}
  {bkts : bucket_array α β n} {sz : ℕ} (a : α) (b : β a)
  (Hnc : ¬ contains_aux a (bkts.read hash_fn a))
  (v : valid bkts sz) : valid (reinsert_aux bkts a b) (sz+1) :=
begin
  have nd := v.nodup (mk_idx n (hash_fn a)),
  refine (v.modify hash_fn
    [] [] [⟨a, b⟩] (bkts.read hash_fn a) rfl rfl (list.nodup_singleton _)
    (λa' e, by simp at e; rw e)
    (λa', false.elim)
    (λa' e1 e2, _)).2,
  simp [-sigma.exists] at e2, subst a',
  exact Hnc ((contains_aux_iff nd).2 e1)
end

theorem valid.erase_aux (a : α) : Π (l : list (Σ a, β a)), a ∈ l.map sigma.fst →
  ∃ (u w : list Σ a, β a) b, l = u ++ [⟨a, b⟩] ++ w ∧ erase_aux a l = u ++ [] ++ w
| []            := false.elim
| (⟨a', b'⟩::t) := begin
  by_cases e : a' = a,
  { subst a',
    simpa [erase_aux, and_comm] using show ∃ u w (x : β a),
      t = u ++ w ∧ (sigma.mk a b') :: t = u ++ ⟨a, x⟩ :: w,
      from ⟨[], t, b', by simp⟩ },
  { simp [erase_aux, e, ne.symm e],
    suffices : ∀ (b : β a) (_ : sigma.mk a b ∈ t), ∃ u w (x : β a),
      (sigma.mk a' b') :: t = u ++ ⟨a, x⟩ :: w ∧
      (sigma.mk a' b') :: (erase_aux a t) = u ++ w,
    { simpa [replace_aux, ne.symm e, e] },
    intros b m,
    have IH : ∀ (x : β a) (_ : sigma.mk a x ∈ t), ∃ u w (x : β a),
      t = u ++ ⟨a, x⟩ :: w ∧ erase_aux a t = u ++ w,
    { simpa using valid.erase_aux t },
    rcases IH b m with ⟨u, w, b'', hl, hfl⟩,
    exact ⟨⟨a', b'⟩ :: u, w, b'', by simp [hl, hfl.symm]⟩ }
end

theorem valid.erase {n} {bkts : bucket_array α β n} {sz}
  (a : α) (Hc : contains_aux a (bkts.read hash_fn a))
  (v : valid bkts sz) : valid (bkts.modify hash_fn a (erase_aux a)) (sz-1) :=
begin
  have nd := v.nodup (mk_idx n (hash_fn a)),
  rcases hash_map.valid.erase_aux a (array.read bkts (mk_idx n (hash_fn a)))
    ((contains_aux_iff nd).1 Hc) with ⟨u, w, b, hl, hfl⟩,
  refine (v.modify hash_fn u [⟨a, b⟩] [] w hl hfl list.nodup_nil _ _ _).2;
  simp
end

end
end hash_map

/-- A hash map data structure, representing a finite key-value map
  with key type `α` and value type `β` (which may depend on `α`). -/
structure hash_map (α : Type u) [decidable_eq α] (β : α → Type v) :=
(hash_fn : α → nat)
(size : ℕ)
(nbuckets : ℕ+)
(buckets : bucket_array α β nbuckets)
(is_valid : hash_map.valid hash_fn buckets size)

/-- Construct an empty hash map with buffer size `nbuckets` (default 8). -/
def mk_hash_map {α : Type u} [decidable_eq α] {β : α → Type v} (hash_fn : α → nat) (nbuckets := 8) :
  hash_map α β :=
let n := if nbuckets = 0 then 8 else nbuckets in
let nz : n > 0 := by abstract { cases nbuckets; simp [if_pos, nat.succ_ne_zero] } in
{ hash_fn  := hash_fn,
  size     := 0,
  nbuckets := ⟨n, nz⟩,
  buckets  := mk_array n [],
  is_valid := hash_map.mk_valid _ _ }

namespace hash_map
variables {α : Type u} {β : α → Type v} [decidable_eq α]

/-- Return the value corresponding to a key, or `none` if not found -/
def find (m : hash_map α β) (a : α) : option (β a) :=
find_aux a (m.buckets.read m.hash_fn a)

/-- Return `tt` if the key exists in the map -/
def contains (m : hash_map α β) (a : α) : bool :=
(m.find a).is_some

instance : has_mem α (hash_map α β) := ⟨λa m, m.contains a⟩

/-- Fold a function over the key-value pairs in the map -/
def fold {δ : Type w} (m : hash_map α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
m.buckets.foldl d f

/-- The list of key-value pairs in the map -/
def entries (m : hash_map α β) : list Σ a, β a :=
m.buckets.as_list

/-- The list of keys in the map -/
def keys (m : hash_map α β) : list α :=
m.entries.map sigma.fst

theorem find_iff (m : hash_map α β) (a : α) (b : β a) :
  m.find a = some b ↔ sigma.mk a b ∈ m.entries :=
m.is_valid.find_aux_iff _

theorem contains_iff (m : hash_map α β) (a : α) :
  m.contains a ↔ a ∈ m.keys :=
m.is_valid.contains_aux_iff _ _

theorem entries_empty (hash_fn : α → nat) (n) :
  (@mk_hash_map α _ β hash_fn n).entries = [] :=
mk_as_list _

theorem keys_empty (hash_fn : α → nat) (n) :
  (@mk_hash_map α _ β hash_fn n).keys = [] :=
by dsimp [keys]; rw entries_empty; refl

theorem find_empty (hash_fn : α → nat) (n a) :
  (@mk_hash_map α _ β hash_fn n).find a = none :=
by induction h : (@mk_hash_map α _ β hash_fn n).find a; [refl,
   { have := (find_iff _ _ _).1 h, rw entries_empty at this, contradiction }]

theorem not_contains_empty (hash_fn : α → nat) (n a) :
  ¬ (@mk_hash_map α _ β hash_fn n).contains a :=
by apply bool_iff_false.2; dsimp [contains]; rw [find_empty]; refl

theorem insert_lemma (hash_fn : α → nat) {n n'}
  {bkts : bucket_array α β n} {sz} (v : valid hash_fn bkts sz) :
  valid hash_fn (bkts.foldl (mk_array _ [] : bucket_array α β n') (reinsert_aux hash_fn)) sz :=
begin
  suffices : ∀ (l : list Σ a, β a) (t : bucket_array α β n') sz,
    valid hash_fn t sz → ((l ++ t.as_list).map sigma.fst).nodup →
    valid hash_fn (l.foldl (λr (a : Σ a, β a), reinsert_aux hash_fn r a.1 a.2) t) (sz + l.length),
  { have p := this bkts.as_list _ _ (mk_valid _ _),
    rw [mk_as_list, list.append_nil, zero_add, v.len] at p,
    rw bucket_array.foldl_eq,
    exact p (v.as_list_nodup _) },
  intro l, induction l with c l IH; intros t sz v nd, {exact v},
  rw show sz + (c :: l).length = sz + 1 + l.length, by simp [add_comm, add_assoc],
  rcases (show (l.map sigma.fst).nodup ∧
      ((bucket_array.as_list t).map sigma.fst).nodup ∧
      c.fst ∉ l.map sigma.fst ∧
      c.fst ∉ (bucket_array.as_list t).map sigma.fst ∧
      (l.map sigma.fst).disjoint ((bucket_array.as_list t).map sigma.fst),
    by simpa [list.nodup_append, not_or_distrib, and_comm, and.left_comm] using nd)
    with ⟨nd1, nd2, nm1, nm2, dj⟩,
  have v' := v.insert _ _ c.2 (λHc, nm2 $ (v.contains_aux_iff _ c.1).1 Hc),
  apply IH _ _ v',
  suffices : ∀ ⦃a : α⦄ (b : β a), sigma.mk a b ∈ l →
    ∀ (b' : β a), sigma.mk a b' ∈ (reinsert_aux hash_fn t c.1 c.2).as_list → false,
  { simpa [list.nodup_append, nd1, v'.as_list_nodup _, list.disjoint] },
  intros a b m1 b' m2,
  rcases (reinsert_aux hash_fn t c.1 c.2).mem_as_list.1 m2 with ⟨i, im⟩,
  have : sigma.mk a b' ∉ array.read t i,
  { intro m3,
    have : a ∈ list.map sigma.fst t.as_list :=
      list.mem_map_of_mem sigma.fst (t.mem_as_list.2 ⟨_, m3⟩),
    exact dj (list.mem_map_of_mem sigma.fst m1) this },
  by_cases h : mk_idx n' (hash_fn c.1) = i,
  { subst h,
    have e : sigma.mk a b' = ⟨c.1, c.2⟩,
    { simpa [reinsert_aux, bucket_array.modify, array.read_write, this] using im },
    injection e with e, subst a,
    exact nm1.elim (@list.mem_map_of_mem _ _ sigma.fst _ _ m1) },
  { apply this,
    simpa [reinsert_aux, bucket_array.modify, array.read_write_of_ne _ _ h] using im }
end

/-- Insert a key-value pair into the map. (Modifies `m` in-place when applicable) -/
def insert : Π (m : hash_map α β) (a : α) (b : β a), hash_map α β
| ⟨hash_fn, size, n, buckets, v⟩ a b :=
let bkt := buckets.read hash_fn a in
if hc : contains_aux a bkt then
{ hash_fn  := hash_fn,
  size     := size,
  nbuckets := n,
  buckets  := buckets.modify hash_fn a (replace_aux a b),
  is_valid := v.replace _ a b hc }
else
let size'    := size + 1,
    buckets' := buckets.modify hash_fn a (λl, ⟨a, b⟩::l),
    valid'   := v.insert _ a b hc in
if size' ≤ n then
{ hash_fn  := hash_fn,
  size     := size',
  nbuckets := n,
  buckets  := buckets',
  is_valid := valid' }
else
let n'        : ℕ+ := ⟨n * 2, mul_pos n.2 dec_trivial⟩,
    buckets'' : bucket_array α β n' :=
                buckets'.foldl (mk_array _ []) (reinsert_aux hash_fn) in
{ hash_fn  := hash_fn,
  size     := size',
  nbuckets := n',
  buckets  := buckets'',
  is_valid := insert_lemma _ valid' }

theorem mem_insert : Π (m : hash_map α β) (a b a' b'),
  (sigma.mk a' b' : sigma β) ∈ (m.insert a b).entries ↔
  if a = a' then b == b' else sigma.mk a' b' ∈ m.entries
| ⟨hash_fn, size, n, bkts, v⟩ a b a' b' := begin
  let bkt := bkts.read hash_fn a,
  have nd : (bkt.map sigma.fst).nodup := v.nodup (mk_idx n (hash_fn a)),
  have lem : Π (bkts' : bucket_array α β n) (v1 u w)
    (hl : bucket_array.as_list bkts = u ++ v1 ++ w)
    (hfl : bucket_array.as_list bkts' = u ++ [⟨a, b⟩] ++ w)
    (veq : (v1 = [] ∧ ¬ contains_aux a bkt) ∨ ∃b'', v1 = [⟨a, b''⟩]),
    sigma.mk a' b' ∈ bkts'.as_list ↔
    if a = a' then b == b' else sigma.mk a' b' ∈ bkts.as_list,
  { intros bkts' v1 u w hl hfl veq,
    rw [hl, hfl],
    by_cases h : a = a',
    { subst a',
      suffices : b = b' ∨ sigma.mk a b' ∈ u ∨ sigma.mk a b' ∈ w ↔ b = b',
      { simpa [eq_comm, or.left_comm] },
      refine or_iff_left_of_imp (not.elim $ not_or_distrib.2 _),
      rcases veq with ⟨rfl, Hnc⟩ | ⟨b'', rfl⟩,
      { have na := (not_iff_not_of_iff $ v.contains_aux_iff _ _).1 Hnc,
        simp [hl, not_or_distrib] at na, simp [na] },
      { have nd' := v.as_list_nodup _,
        simp [hl, list.nodup_append] at nd', simp [nd'] } },
    { suffices : sigma.mk a' b' ∉ v1, {simp [h, ne.symm h, this]},
      rcases veq with ⟨rfl, Hnc⟩ | ⟨b'', rfl⟩; simp [ne.symm h] } },
  by_cases Hc : (contains_aux a bkt : Prop),
  { rcases hash_map.valid.replace_aux a b (array.read bkts (mk_idx n (hash_fn a)))
      ((contains_aux_iff nd).1 Hc) with ⟨u', w', b'', hl', hfl'⟩,
    rcases (append_of_modify u' [⟨a, b''⟩] [⟨a, b⟩] w' hl' hfl') with ⟨u, w, hl, hfl⟩,
    simpa [insert, @dif_pos (contains_aux a bkt) _ Hc]
      using lem _ _ u w hl hfl (or.inr ⟨b'', rfl⟩) },
  { let size' := size + 1,
    let bkts' := bkts.modify hash_fn a (λl, ⟨a, b⟩::l),
    have mi : sigma.mk a' b' ∈ bkts'.as_list ↔
        if a = a' then b == b' else sigma.mk a' b' ∈ bkts.as_list :=
      let ⟨u, w, hl, hfl⟩ := append_of_modify [] [] [⟨a, b⟩] _ rfl rfl in
      lem bkts' _ u w hl hfl $ or.inl ⟨rfl, Hc⟩,
    simp [insert, @dif_neg (contains_aux a bkt) _ Hc],
    by_cases h : size' ≤ n,
    -- TODO(Mario): Why does the by_cases assumption look different than the stated one?
    { simpa [show size' ≤ n, from h] using mi },
    { let n' : ℕ+ := ⟨n * 2, mul_pos n.2 dec_trivial⟩,
      let bkts'' : bucket_array α β n' := bkts'.foldl (mk_array _ []) (reinsert_aux hash_fn),
      suffices : sigma.mk a' b' ∈ bkts''.as_list ↔ sigma.mk a' b' ∈ bkts'.as_list.reverse,
      { simpa [show ¬ size' ≤ n, from h, mi] },
      rw [show bkts'' = bkts'.as_list.foldl _ _, from bkts'.foldl_eq _ _,
          ← list.foldr_reverse],
      induction bkts'.as_list.reverse with a l IH,
      { simp [mk_as_list] },
      { cases a with a'' b'',
        let B := l.foldr (λ (y : sigma β) (x : bucket_array α β n'),
          reinsert_aux hash_fn x y.1 y.2) (mk_array n' []),
        rcases append_of_modify [] [] [⟨a'', b''⟩] _ rfl rfl with ⟨u, w, hl, hfl⟩,
        simp [IH.symm, or.left_comm, show B.as_list = _, from hl,
              show (reinsert_aux hash_fn B a'' b'').as_list = _, from hfl] } } }
end

theorem find_insert_eq (m : hash_map α β) (a : α) (b : β a) : (m.insert a b).find a = some b :=
(find_iff (m.insert a b) a b).2 $ (mem_insert m a b a b).2 $ by rw if_pos rfl

theorem find_insert_ne (m : hash_map α β) (a a' : α) (b : β a) (h : a ≠ a') :
  (m.insert a b).find a' = m.find a' :=
option.eq_of_eq_some $ λb',
let t := mem_insert m a b a' b' in
(find_iff _ _ _).trans $ iff.trans (by rwa if_neg h at t) (find_iff _ _ _).symm

theorem find_insert (m : hash_map α β) (a' a : α) (b : β a) :
  (m.insert a b).find a' = if h : a = a' then some (eq.rec_on h b) else m.find a' :=
if h : a = a' then by rw dif_pos h; exact
  match a', h with ._, rfl := find_insert_eq m a b end
else by rw dif_neg h; exact find_insert_ne m a a' b h

/-- Insert a list of key-value pairs into the map. (Modifies `m` in-place when applicable) -/
def insert_all (l : list (Σ a, β a)) (m : hash_map α β) : hash_map α β :=
l.foldl (λ m ⟨a, b⟩, insert m a b) m

/-- Construct a hash map from a list of key-value pairs. -/
def of_list (l : list (Σ a, β a)) (hash_fn) : hash_map α β :=
insert_all l (mk_hash_map hash_fn (2 * l.length))

/-- Remove a key from the map. (Modifies `m` in-place when applicable) -/
def erase (m : hash_map α β) (a : α) : hash_map α β :=
match m with ⟨hash_fn, size, n, buckets, v⟩ :=
  if hc : contains_aux a (buckets.read hash_fn a) then
  { hash_fn  := hash_fn,
    size     := size - 1,
    nbuckets := n,
    buckets  := buckets.modify hash_fn a (erase_aux a),
    is_valid := v.erase _ a hc }
  else m
end

theorem mem_erase : Π (m : hash_map α β) (a a' b'),
  (sigma.mk a' b' : sigma β) ∈ (m.erase a).entries ↔
  a ≠ a' ∧ sigma.mk a' b' ∈ m.entries
| ⟨hash_fn, size, n, bkts, v⟩ a a' b' := begin
  let bkt := bkts.read hash_fn a,
  by_cases Hc : (contains_aux a bkt : Prop),
  { let bkts' := bkts.modify hash_fn a (erase_aux a),
    suffices : sigma.mk a' b' ∈ bkts'.as_list ↔ a ≠ a' ∧ sigma.mk a' b' ∈ bkts.as_list,
    { simpa [erase, @dif_pos (contains_aux a bkt) _ Hc] },
    have nd := v.nodup (mk_idx n (hash_fn a)),
    rcases valid.erase_aux a bkt ((contains_aux_iff nd).1 Hc) with ⟨u', w', b, hl', hfl'⟩,
    rcases append_of_modify u' [⟨a, b⟩] [] _ hl' hfl' with ⟨u, w, hl, hfl⟩,
    suffices : ∀_:sigma.mk a' b' ∈ u ∨ sigma.mk a' b' ∈ w, a ≠ a',
    { have : sigma.mk a' b' ∈ u ∨ sigma.mk a' b' ∈ w ↔ (¬a = a' ∧ a' = a) ∧ b' == b ∨
        ¬a = a' ∧ (sigma.mk a' b' ∈ u ∨ sigma.mk a' b' ∈ w),
      { simp [eq_comm, not_and_self_iff, and_iff_right_of_imp this] },
      simpa [hl, show bkts'.as_list = _, from hfl, and_or_distrib_left,
             and_comm, and.left_comm, or.left_comm] },
    intros m e, subst a', revert m, apply not_or_distrib.2,
    have nd' := v.as_list_nodup _,
    simp [hl, list.nodup_append] at nd', simp [nd'] },
  { suffices : ∀_:sigma.mk a' b' ∈ bucket_array.as_list bkts, a ≠ a',
    { simp [erase, @dif_neg (contains_aux a bkt) _ Hc, entries, and_iff_right_of_imp this] },
    intros m e, subst a',
    exact Hc ((v.contains_aux_iff _ _).2 (list.mem_map_of_mem sigma.fst m)) }
end

theorem find_erase_eq (m : hash_map α β) (a : α) : (m.erase a).find a = none :=
begin
  cases h : (m.erase a).find a with b, {refl},
  exact absurd rfl ((mem_erase m a a b).1 ((find_iff (m.erase a) a b).1 h)).left
end

theorem find_erase_ne (m : hash_map α β) (a a' : α) (h : a ≠ a') :
  (m.erase a).find a' = m.find a' :=
option.eq_of_eq_some $ λb',
(find_iff _ _ _).trans $ (mem_erase m a a' b').trans $
  (and_iff_right h).trans (find_iff _ _ _).symm

theorem find_erase (m : hash_map α β) (a' a : α) :
  (m.erase a).find a' = if a = a' then none else m.find a' :=
if h : a = a' then by subst a'; simp [find_erase_eq m a]
else by rw if_neg h; exact find_erase_ne m a a' h

section string
variables [has_to_string α] [∀ a, has_to_string (β a)]
open prod
private def key_data_to_string (a : α) (b : β a) (first : bool) : string :=
(if first then "" else ", ") ++ sformat!"{a} ← {b}"

private def to_string (m : hash_map α β) : string :=
"⟨" ++ (fst (fold m ("", tt) (λ p a b, (fst p ++ key_data_to_string a b (snd p), ff)))) ++ "⟩"

instance : has_to_string (hash_map α β) :=
⟨to_string⟩

end string

section format
open format prod
variables [has_to_format α] [∀ a, has_to_format (β a)]

private meta def format_key_data (a : α) (b : β a) (first : bool) : format :=
(if first then to_fmt "" else to_fmt "," ++ line) ++
  to_fmt a ++ space ++ to_fmt "←" ++ space ++ to_fmt b

private meta def to_format (m : hash_map α β) : format :=
group $ to_fmt "⟨" ++
  nest 1 (fst (fold m (to_fmt "", tt) (λ p a b, (fst p ++ format_key_data a b (snd p), ff)))) ++
  to_fmt "⟩"

meta instance : has_to_format (hash_map α β) :=
⟨to_format⟩
end format

/-- `hash_map` with key type `nat` and value type that may vary. -/
instance {β : ℕ → Type*} : inhabited (hash_map ℕ β) := ⟨mk_hash_map id⟩

end hash_map
