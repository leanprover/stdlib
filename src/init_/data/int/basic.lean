/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Instances, copied from the core library by Johan Commelin
-/

import algebra.ring

instance : comm_ring int :=
{ add            := int.add,
  add_assoc      := int.add_assoc,
  zero           := int.zero,
  zero_add       := int.zero_add,
  neg            := int.neg,
  add_left_neg   := int.add_left_neg,
  add_comm       := int.add_comm,
  mul            := int.mul,
  mul_assoc      := int.mul_assoc,
  one            := int.one,
  one_mul        := int.one_mul,
  mul_one        := int.mul_one,
  left_distrib   := int.distrib_left,
  right_distrib  := int.distrib_right,
  mul_comm       := int.mul_comm }

/- Extra instances to short-circuit type class resolution -/
-- instance : has_sub int            := by apply_instance -- This is in core
instance : add_comm_monoid int    := by apply_instance
instance : add_monoid int         := by apply_instance
instance : monoid int             := by apply_instance
instance : comm_monoid int        := by apply_instance
instance : comm_semigroup int     := by apply_instance
instance : semigroup int          := by apply_instance
instance : add_comm_semigroup int := by apply_instance
instance : add_semigroup int      := by apply_instance
instance : comm_semiring int      := by apply_instance
instance : semiring int           := by apply_instance
instance : ring int               := by apply_instance
instance : distrib int            := by apply_instance

instance : zero_ne_one_class ℤ :=
{ zero := 0, one := 1, zero_ne_one := int.zero_ne_one }
