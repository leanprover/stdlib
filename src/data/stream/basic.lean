/-
Copyright (c) 2020 Gabriel Ebner, Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Simon Hudon
-/
import data.stream
import data.list.range

/-!
# Additional instances and attributes for streams
-/

attribute [ext] stream.ext

instance {α} [inhabited α] : inhabited (stream α) :=
⟨stream.const (default _)⟩

namespace stream
open nat

/-- `take s n` returns a list of the `n` first elements of stream `s` -/
def take {α} (s : stream α) (n : ℕ) : list α :=
(list.range n).map s

lemma length_take {α} (s : stream α) (n : ℕ) : (take s n).length = n :=
by simp [take]

/-- Use a state monad to generate a stream through corecursion -/
def corec_state {σ α} (cmd : state σ α) (s : σ) : stream α :=
stream.corec prod.fst (cmd.run ∘ prod.snd) (cmd.run s)

end stream
