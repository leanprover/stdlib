/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import data.option.defs
import data.list.defs

/-!
# rb_map

This file defines additional operations on native rb_maps and rb_sets.
These structures are defined in core in `init.meta.rb_map`. They are meta objects,
and are generally the most efficient dictionary structures to use for pure metaprogramming right now.
-/

namespace native

/-! ### Declarations about `rb_set` -/
namespace rb_set

meta instance {key} [has_lt key] [decidable_rel ((<) : key → key → Prop)] :
  inhabited (rb_set key) :=
⟨mk_rb_set⟩

/-- `filter s P` returns the subset of elements of `s` satisfying `P`. -/
meta def filter {key} (s : rb_set key) (P : key → bool) : rb_set key :=
s.fold s (λ a m, if P a then m else m.erase a)

/-- `mfilter s P` returns the subset of elements of `s` satisfying `P`,
where the check `P` is monadic. -/
meta def mfilter {m} [monad m] {key} (s : rb_set key) (P : key → m bool) : m (rb_set key) :=
s.fold (pure s) (λ a m,
  do x ← m,
     mcond (P a) (pure x) (pure $ x.erase a))

/-- `union s t` returns an rb_set containing every element that appears in either `s` or `t`. -/
meta def union {key} (s t : rb_set key) : rb_set key :=
s.fold t (λ a t, t.insert a)

/--
`of_list_core empty l` turns a list of keys into an `rb_set`.
It takes a user_provided `rb_set` to use for the base case.
This can be used to pre-seed the set with additional elements,
and/or to use a custom comparison operator.
-/
meta def of_list_core {key} (base : rb_set key) : list key → rb_map key unit
| []      := base
| (x::xs) := rb_set.insert (of_list_core xs) x

/--
`of_list l` transforms a list `l : list key` into an `rb_set`,
inferring an order on the type `key`.
-/
meta def of_list {key} [has_lt key] [decidable_rel ((<) : key → key → Prop)] :
  list key → rb_set key :=
of_list_core mk_rb_set

/--
`sdiff s1 s2` returns the set of elements that are in `s1` but not in `s2`.
It does so by folding over `s2`. If `s1` is significantly smaller than `s2`,
it may be worth it to reverse the fold.
-/
meta def sdiff {α} (s1 s2 : rb_set α) : rb_set α :=
s2.fold s1 $ λ v s, s.erase v

/--
`insert_list s l` inserts each element of `l` into `s`.
-/
meta def insert_list {key} (s : rb_set key) (l : list key) : rb_set key :=
l.foldl rb_set.insert s

end rb_set

/-! ### Declarations about `rb_map` -/

namespace rb_map

meta instance {key data : Type} [has_lt key] [decidable_rel ((<) : key → key → Prop)] :
  inhabited (rb_map key data) :=
⟨mk_rb_map⟩

/-- `find_def default m k` returns the value corresponding to `k` in `m`, if it exists.
Otherwise it returns `default`. -/
meta def find_def {key value} (default : value) (m : rb_map key value) (k : key) :=
(m.find k).get_or_else default

/-- `ifind m key` returns the value corresponding to `key` in `m`, if it exists.
Otherwise it returns the default value of `value`. -/
meta def ifind {key value} [inhabited value] (m : rb_map key value) (k : key) : value :=
(m.find k).iget

/-- `zfind m key` returns the value corresponding to `key` in `m`, if it exists.
Otherwise it returns 0. -/
meta def zfind {key value} [has_zero value] (m : rb_map key value) (k : key) : value :=
(m.find k).get_or_else 0

/-- Returns the pointwise sum of `m1` and `m2`, treating nonexistent values as 0. -/
meta def add {key value} [has_add value] [has_zero value] [decidable_eq value]
  (m1 m2 : rb_map key value) : rb_map key value :=
m1.fold m2
  (λ n v m,
   let nv := v + m2.zfind n in
   if nv = 0 then m.erase n else m.insert n nv)

variables {m : Type → Type*} [monad m]
open function

/-- `mfilter P s` filters `s` by the monadic predicate `P` on keys and values. -/
meta def mfilter {key val} [has_lt key] [decidable_rel ((<) : key → key → Prop)]
  (P : key → val → m bool) (s : rb_map key val) : m (rb_map.{0 0} key val) :=
rb_map.of_list <$> s.to_list.mfilter (uncurry P)

/-- `mmap f s` maps the monadic function `f` over values in `s`. -/
meta def mmap {key val val'} [has_lt key] [decidable_rel ((<) : key → key → Prop)]
  (f : val → m val') (s : rb_map key val) : m (rb_map.{0 0} key val') :=
rb_map.of_list <$> s.to_list.mmap (λ ⟨a,b⟩, prod.mk a <$> f b)

/-- `scale b m` multiplies every value in `m` by `b`. -/
meta def scale {key value} [has_lt key] [decidable_rel ((<) : key → key → Prop)] [has_mul value]
  (b : value) (m : rb_map key value) : rb_map key value :=
m.map ((*) b)

section
open format prod
variables {key : Type} {data data' : Type} [has_to_tactic_format key] [has_to_tactic_format data]
private meta def pp_key_data (k : key) (d : data) (first : bool) : tactic format :=
do fk ← tactic.pp k, fd ← tactic.pp d, return $
(if first then to_fmt "" else to_fmt "," ++ line) ++ fk ++ space ++ to_fmt "←" ++ space ++ fd

meta instance : has_to_tactic_format (rb_map key data) :=
⟨λ m, do
  (fmt, _) ← fold m (return (to_fmt "", tt))
     (λ k d p, do p ← p, pkd ← pp_key_data k d (snd p), return (fst p ++ pkd, ff)),
  return $ group $ to_fmt "⟨" ++ nest 1 fmt ++ to_fmt "⟩"⟩

variables [has_lt key] [decidable_rel ((<) : key → key → Prop)]
variables (f : data → data → data)

meta def filter_map (f : key → data → option data') (x : rb_map key data) : rb_map key data' :=
fold x (mk _ _) $ λa b m', (insert m' a <$> f a b).get_or_else m'

meta def intersect_with (m m' : rb_map key data) : rb_map key data :=
m.filter_map $ λ k x, f x <$> m'.find k

meta def intersect (x y : rb_map key data) : rb_map key data :=
intersect_with (function.const data) x y

meta def difference (m m' : rb_map key data) : rb_map key data :=
m.filter_map (λ k x, guard (¬ m'.contains k) >> pure x)

end

end rb_map

/-! ### Declarations about `rb_lmap` -/

namespace rb_lmap

meta instance (key : Type) [has_lt key] [decidable_rel ((<) : key → key → Prop)] (data : Type) :
  inhabited (rb_lmap key data) :=
⟨rb_lmap.mk _ _⟩

/-- Construct a rb_lmap from a list of key-data pairs -/
protected meta def of_list {key : Type} {data : Type} [has_lt key]
  [decidable_rel ((<) : key → key → Prop)] : list (key × data) → rb_lmap key data
| []           := rb_lmap.mk key data
| ((k, v)::ls) := (of_list ls).insert k v

/-- Returns the list of values of an `rb_lmap`. -/
protected meta def values {key data} (m : rb_lmap key data) : list data :=
m.fold [] (λ _, (++))

end rb_lmap
end native

/-! ### Declarations about `name_set` -/

namespace name_set

meta instance : inhabited name_set := ⟨mk_name_set⟩

/-- `filter P s` returns the subset of elements of `s` satisfying `P`. -/
meta def filter (P : name → bool) (s : name_set) : name_set :=
s.fold s (λ a m, if P a then m else m.erase a)

/-- `mfilter P s` returns the subset of elements of `s` satisfying `P`,
where the check `P` is monadic. -/
meta def mfilter {m} [monad m] (P : name → m bool) (s : name_set) : m name_set :=
s.fold (pure s) (λ a m,
  do x ← m,
     mcond (P a) (pure x) (pure $ x.erase a))

/-- `mmap f s` maps the monadic function `f` over values in `s`. -/
meta def mmap {m} [monad m] (f : name → m name) (s : name_set) : m name_set :=
s.fold (pure mk_name_set) (λ a m,
  do x ← m,
     b ← f a,
     (pure $ x.insert b))

/-- `union s t` returns an rb_set containing every element that appears in either `s` or `t`. -/
meta def union (s t : name_set) : name_set :=
s.fold t (λ a t, t.insert a)

/-- `insert_list s l` inserts every element of `l` into `s`. -/
meta def insert_list (s : name_set) (l : list name) : name_set :=
l.foldr (λ n s', s'.insert n) s

end name_set

/-! ### Declarations about `name_map` -/

namespace name_map

meta instance {data : Type} : inhabited (name_map data) :=
⟨mk_name_map⟩

end name_map

meta def list.to_rb_set {α} [has_lt α] [decidable_rel ((<) : α → α → Prop)] (xs : list α) : native.rb_set α :=
xs.foldl native.rb_set.insert (native.mk_rb_set)
