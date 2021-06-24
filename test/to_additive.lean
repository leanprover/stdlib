import tactic
import algebra.group.units

example : (add_units.mk_of_add_eq_zero 0 0 (by simp) : ℕ) = (add_units.mk_of_add_eq_zero 0 0 (by simp) : ℕ) :=
by norm_cast
