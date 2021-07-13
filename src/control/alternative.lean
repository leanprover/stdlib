import control.fold

universes u v

namespace alternative

  section
    variables  {T S : Type u → Type u} [applicative T] [alternative S]
    instance : alternative (T ∘ S) :=
    { pure    := λ α x, (pure (pure x) : T (S _)),
      failure := λ x, (pure $ failure : T (S _)),
      seq     := λ α β f x, show T(S β), from pure (<*>) <*> f <*> x,
      orelse  := λ α a b, show T(S α), from pure (<|>) <*> a <*> b
    }
  end

  variables {T : Type u → Type v} [alternative T] {α β : Type u}

  def returnopt : option α → T α
  | none := failure
  | (some x) := pure x

  def optreturn : T α → T (option α)
  | t := (some <$> t) <|> (pure none)

  def is_ok {T : Type → Type v} [alternative T] {α : Type}:  T α → T (bool)
  | t := (t *> pure (tt)) <|> pure (ff)

  def mguard {T : Type → Type v} [alternative T] [monad T]: T bool → T unit
  | c := do b ← c, if b then pure () else failure

  variables [monad T]

  meta def repeat (t : T α) : T (list α) :=
  (pure list.cons <*> t <*> (pure punit.star >>= λ _, repeat)) <|> pure []

end alternative
