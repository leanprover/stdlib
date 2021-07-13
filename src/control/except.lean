universes u v

def except.flip {ε : Type u} {α : Type v} : except ε α → except α ε
| e := except.rec except.ok except.error e

instance monad_except.of_statet {ε σ} {m : Type → Type} [monad m] [monad_except ε m] : monad_except ε (state_t σ m) :=
{ throw := λ α e, state_t.lift $ throw e
, catch := λ α S e, ⟨λ s, catch (state_t.run S s) (λ x, state_t.run (e x) s)⟩ -- [note] alternatively, you could propagate the state.
}

instance monad_except.alt {ε} [inhabited ε] {m : Type → Type} [monad m] [monad_except ε m] : alternative m :=
{ failure := λ α,throw $ inhabited.default ε
, orelse := λ α x y, monad_except.orelse x y
}
