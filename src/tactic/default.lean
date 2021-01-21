/-
This file imports many useful tactics ("the kitchen sink").

You can use `import tactic` at the beginning of your file to get everything.
(Although you may want to strip things down when you're polishing.)

Because this file imports some complicated tactics, it has many transitive dependencies
(which of course may not use `import tactic`, and must import selectively).

As (non-exhaustive) examples, these includes things like:
* algebra.group_power
* algebra.ordered_ring
* data.rat
* data.nat.prime
* data.list.perm
* data.set.lattice
* data.equiv.encodable.basic
* order.complete_lattice
-/
import tactic.basic -- ensure basic tactics are available
import tactic.ring_exp
import tactic.noncomm_ring
import tactic.linarith
import tactic.omega
import tactic.tfae
import tactic.apply_fun
import tactic.interval_cases
import tactic.reassoc_axiom -- most likely useful only for category_theory
import tactic.slice
import tactic.subtype_instance
import tactic.derive_fintype
import tactic.group
import tactic.transport
import tactic.unfold_cases
