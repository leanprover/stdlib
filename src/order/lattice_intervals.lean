/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson.
-/

import data.set.intervals.basic

/-!
# Intervals in Lattices

In this file, we provide instances of lattice structures on intervals within lattices.
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances. These are probably not all of the lattice instances that could be placed on these
intervals, but more can be added easily along the same lines when needed.

## Main definitions
In the following, `*` can represent either `c`, `o`, or `i`.
  * `set.Ic*.semilattice_inf_bot`
  * `set.Ii*.semillatice_inf`
  * `set.I*c.semilattice_sup_top`
  * `set.I*c.semillatice_inf`
  * `set.Iic.bounded_lattice`, within a `bounded_lattice`
  * `set.Ici.bounded_lattice`, within a `bounded_lattice`

-/

variable {α : Type*}

namespace set

namespace Ico

variables {a b : α}

instance [semilattice_inf α] : semilattice_inf (Ico a b) :=
subtype.semilattice_inf (λ x y hx hy, ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩)

/-- `Ico a b` has a bottom element whenever `a < b`. -/
def order_bot [partial_order α] (h : a < b) : order_bot (Ico a b) :=
{ bot := ⟨a, ⟨le_refl a, h⟩⟩,
  bot_le := λ x, x.prop.1,
  .. (subtype.partial_order _) }

/-- `Ico a b` is a `semilattice_inf_bot` whenever `a < b`. -/
def semilattice_inf_bot [semilattice_inf α] (h : a < b) : semilattice_inf_bot (Ico a b) :=
{ .. (Ico.semilattice_inf), .. (Ico.order_bot h) }

end Ico

namespace Iio

instance [semilattice_inf α] {a : α} : semilattice_inf (Iio a) :=
subtype.semilattice_inf (λ x y hx hy, lt_of_le_of_lt inf_le_left hx)

end Iio

namespace Ioc

variables {a b : α}

instance [semilattice_sup α] : semilattice_sup (Ioc a b) :=
subtype.semilattice_sup (λ x y hx hy, ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩)

/-- `Ioc a b` has a top element whenever `a < b`. -/
def order_top [partial_order α] (h : a < b) : order_top (Ioc a b) :=
{ top := ⟨b, ⟨h, le_refl b⟩⟩,
  le_top := λ x, x.prop.2,
  .. (subtype.partial_order _) }

/-- `Ioc a b` is a `semilattice_sup_top` whenever `a < b`. -/
def semilattice_sup_top [semilattice_sup α] (h : a < b) : semilattice_sup_top (Ioc a b) :=
{ .. (Ioc.semilattice_sup), .. (Ioc.order_top h) }

end Ioc

namespace Iio

instance [semilattice_sup α] {a : α} : semilattice_sup (Ioi a) :=
subtype.semilattice_sup (λ x y hx hy, lt_of_lt_of_le hx le_sup_left)

end Iio

namespace Iic

variables {a : α}

instance [semilattice_inf α] : semilattice_inf (Iic a) :=
subtype.semilattice_inf (λ x y hx hy, le_trans inf_le_left hx)

instance [semilattice_sup α] : semilattice_sup (Iic a) :=
subtype.semilattice_sup (λ x y hx hy, sup_le hx hy)

instance [lattice α] : lattice (Iic a) :=
{ .. (Iic.semilattice_inf),
  .. (Iic.semilattice_sup) }

instance [partial_order α] : order_top (Iic a) :=
{ top := ⟨a, le_refl a⟩,
  le_top := λ x, x.prop,
  .. (subtype.partial_order _) }

@[simp] lemma coe_top [partial_order α] {a : α} : ↑(⊤ : Iic a) = a := rfl

instance [semilattice_inf α] : semilattice_inf_top (Iic a) :=
{ .. (Iic.semilattice_inf),
  .. (Iic.order_top) }

instance [semilattice_sup α] : semilattice_sup_top (Iic a) :=
{ .. (Iic.semilattice_sup),
  .. (Iic.order_top) }

instance [order_bot α] : order_bot (Iic a) :=
{ bot := ⟨⊥, bot_le⟩,
  bot_le := λ ⟨_,_⟩, subtype.mk_le_mk.2 bot_le,
  .. (infer_instance : partial_order (Iic a)) }

@[simp] lemma coe_bot [order_bot α] {a : α} : ↑(⊥ : Iic a) = (⊥ : α) := rfl

instance [semilattice_inf_bot α] : semilattice_inf_bot (Iic a) :=
{ .. (Iic.semilattice_inf),
  .. (Iic.order_bot) }

instance [semilattice_sup_bot α] : semilattice_sup_bot (Iic a) :=
{ .. (Iic.semilattice_sup),
  .. (Iic.order_bot) }

instance [bounded_lattice α] : bounded_lattice (Iic a) :=
{ .. (Iic.order_top),
  .. (Iic.order_bot),
  .. (Iic.lattice) }
end Iic

namespace Ici

variables {a : α}

instance [semilattice_inf α] : semilattice_inf (Ici a) :=
subtype.semilattice_inf (λ x y hx hy, le_inf hx hy)

instance [semilattice_sup α] : semilattice_sup (Ici a) :=
subtype.semilattice_sup (λ x y hx hy, le_trans hx le_sup_left)

instance [lattice α] : lattice (Ici a) :=
{ .. (Ici.semilattice_inf),
  .. (Ici.semilattice_sup) }

instance [partial_order α] : order_bot (Ici a) :=
{ bot := ⟨a, le_refl a⟩,
  bot_le := λ x, x.prop,
  .. (subtype.partial_order _) }

@[simp] lemma coe_bot [partial_order α] {a : α} : ↑(⊥ : Ici a) = a := rfl

instance [semilattice_inf α] : semilattice_inf_bot (Ici a) :=
{ .. (Ici.semilattice_inf),
  .. (Ici.order_bot) }

instance [semilattice_sup α] : semilattice_sup_bot (Ici a) :=
{ .. (Ici.semilattice_sup),
  .. (Ici.order_bot) }

instance [order_top α] : order_top (Ici a) :=
{ top := ⟨⊤, le_top⟩,
  le_top := λ ⟨_,_⟩, subtype.mk_le_mk.2 le_top,
  .. (infer_instance : partial_order (Ici a)) }

@[simp] lemma coe_top [order_top α] {a : α} : ↑(⊤ : Ici a) = (⊤ : α) := rfl

instance [semilattice_sup_top α] : semilattice_sup_top (Ici a) :=
{ .. (Ici.semilattice_sup),
  .. (Ici.order_top) }

instance [semilattice_inf_top α] : semilattice_inf_top (Ici a) :=
{ .. (Ici.semilattice_inf),
  .. (Ici.order_top) }

instance [bounded_lattice α] : bounded_lattice (Ici a) :=
{ .. (Ici.order_top),
  .. (Ici.order_bot),
  .. (Ici.lattice) }

end Ici

namespace Icc

instance [semilattice_inf α] {a b : α} : semilattice_inf (Icc a b) :=
subtype.semilattice_inf (λ x y hx hy, ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩)

instance [semilattice_sup α] {a b : α} : semilattice_sup (Icc a b) :=
subtype.semilattice_sup (λ x y hx hy, ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩)

instance [lattice α] {a b : α} : lattice (Icc a b) :=
{ .. (Icc.semilattice_inf),
  .. (Icc.semilattice_sup) }

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
def order_bot [partial_order α] {a b : α} (h : a ≤ b) : order_bot (Icc a b) :=
{ bot := ⟨a, ⟨le_refl a, h⟩⟩,
  bot_le := λ x, x.prop.1,
  .. (subtype.partial_order _) }

/-- `Icc a b` has a top element whenever `a ≤ b`. -/
def order_top [partial_order α] {a b : α} (h : a ≤ b) : order_top (Icc a b) :=
{ top := ⟨b, ⟨h, le_refl b⟩⟩,
  le_top := λ x, x.prop.2,
  .. (subtype.partial_order _) }

/-- `Icc a b` is a `semilattice_inf_bot` whenever `a ≤ b`. -/
def semilattice_inf_bot [semilattice_inf α] {a b : α} (h : a ≤ b) :
  semilattice_inf_bot (Icc a b) :=
{ .. (Icc.order_bot h),
  .. (Icc.semilattice_inf) }

/-- `Icc a b` is a `semilattice_inf_top` whenever `a ≤ b`. -/
def semilattice_inf_top [semilattice_inf α] {a b : α} (h : a ≤ b) :
  semilattice_inf_top (Icc a b) :=
{ .. (Icc.order_top h),
  .. (Icc.semilattice_inf) }

/-- `Icc a b` is a `semilattice_sup_bot` whenever `a ≤ b`. -/
def semilattice_sup_bot [semilattice_sup α] {a b : α} (h : a ≤ b) :
  semilattice_sup_bot (Icc a b) :=
{ .. (Icc.order_bot h),
  .. (Icc.semilattice_sup) }

/-- `Icc a b` is a `semilattice_sup_top` whenever `a ≤ b`. -/
def semilattice_sup_top [semilattice_sup α] {a b : α} (h : a ≤ b) :
  semilattice_sup_top (Icc a b) :=
{ .. (Icc.order_top h),
  .. (Icc.semilattice_sup) }

/-- `Icc a b` is a `bounded_lattice` whenever `a ≤ b`. -/
def bounded_lattice [lattice α] {a b : α} (h : a ≤ b) :
  bounded_lattice (Icc a b) :=
{ .. (Icc.semilattice_inf_bot h),
  .. (Icc.semilattice_sup_top h) }

end Icc

end set
