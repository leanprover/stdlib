/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import tactic.basic

/-!
# Bundled right inverse (section)

In this file we implement the bundled version of a right inverse function. The final purpose of
this type is to conviniently implement sections of bundles.

## Implementation notes

Let `E : B → Type*` be the collection of fibers of a bundle on `B`.
In the case of sections of bundles we prove that the type of right inverses of `bundle.proj E` is
equivalent to the type `Π x : B, E x`. Both implementations of sections have their advantages:
`right_inv (proj E)` is better to talk about properties such as continuity, whereas `Π x : B, E x`
works better with algebraic structures: it naturally inherits the algebraic structures present on
the fibers, thanks to the `Π` instances. It is hence a good idea to implement both and write down
the equivalence between them, but then we have to choose only one for our final implementation of
sections. We chose `right_inv (proj E)` because it is more general (some of the results in the
theory of sections are true for `right_inv f`, for a generic `f`), and it has a more natural
coercion to a function `B → bundle.total_space E` which is finally what we want. Note that we could
also register a coercion to `B → bundle.total_space E` from `Π x : B, E x`, and it is not a bad idea
to implement things this way, but it is just slightly more clumsy: in the case of continuous
sections, in the first case one can implement continuous sections as
`structure continuous_section (f : α → β) extends right_inv f, C(β, α)`
whereas in the second way one would have to write continuity manually; it is not a big deal but the
first way is slightly more natural. Also note that to recover the value of the section on the fiber
in the first way one can use `.2` whereas the second way would make use of coercions.

-/

/-- Bundled right inverse of a function. Note that here the `nolint` has a true mathematical
meaning: the structure is inhabited iff the function is surjective. -/
@[nolint has_inhabited_instance]
structure right_inv {α: Type*} {β: Type*} (f : α → β) :=
(to_fun : β → α)
(right_inv' : function.right_inverse to_fun f)

namespace right_inv

variables {α: Type*} {β: Type*} {f : α → β} {g h : right_inv f}

instance : has_coe_to_fun (right_inv f) := ⟨_, right_inv.to_fun⟩

@[simp] lemma to_fun_eq_coe (g : right_inv f) : g.to_fun = ⇑g := rfl

lemma coe_injective (H : ⇑g = h) : g = h :=
by { cases g, cases h, congr' }

@[ext] theorem ext (H : ∀ a, g a = h a) : g = h :=
coe_injective $ funext H

lemma right_inv_def {f : α → β} (g : right_inv f) : f ∘ g = id := g.right_inv'.id

lemma right_inverse {f : α → β} (g : right_inv f) : function.right_inverse g f := g.right_inv'

lemma surjective {f : α → β} (g : right_inv f) : function.surjective f := g.right_inverse.surjective

end right_inv
