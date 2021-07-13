/- Author: E.W.Ayers © 2019
-/
import meta.assignable control.except

open assignable

universes u v

/-!
A zipper is a structure that lets you navigate through a recursive datastructure such as a list.
This is a zipper for expressions, but it also does some context management for you so that your algorithms can work under binders.
http://www.st.cs.uni-sb.de/edu/seminare/2005/advanced-fp/docs/huet-zipper.pdf
-/

namespace expr

instance coord.dec_lt : decidable_rel ((<) : coord → coord → Prop) :=
by apply_instance

instance address.has_lt : has_lt address :=
list.has_lt

instance address.dec_lt : decidable_rel ((<) : address → address → Prop) :=
list.has_decidable_lt

/-- Checks whether the following the coordinate will cause the context to change. -/
meta def coord.is_binding : coord → bool
| coord.pi_body := tt | coord.lam_body := tt | coord.elet_body := tt
| _ := ff

/-- Returns the set of coordinates that are valid for a given expression. -/
meta def get_coords : expr → list coord
| (expr.app  _ _)     := [coord.app_fn, coord.app_arg]
| (expr.pi   _ _ _ _) := [coord.pi_var_type, coord.pi_body]
| (expr.lam  _ _ _ _) := [coord.lam_var_type, coord.lam_body]
| (expr.elet _ _ _ _) := [coord.elet_var_type, coord.elet_assignment, coord.elet_body]
| _ := []

/-- Perform `g` on the subexpression specified by the coordinate and return the parent expression with this modified child.
The list of binders provided to `g` has the most recently followed binder as the head,
so `expr.var 0` corresponds to the head of the binder list. -/
meta def expr.coord.modify {t} [alternative t] (g : telescope → expr → t expr): coord → expr → t expr
| (coord.app_fn)          (expr.app f a)         := pure expr.app <*> g [] f <*> pure a
| (coord.app_arg)         (expr.app f a)         := pure expr.app <*> pure f <*> g [] a
| (coord.lam_var_type)    (expr.lam  n bi y   b) := pure (expr.lam n bi) <*> g [] y <*> pure b
| (coord.lam_body)        (expr.lam  n bi y   b) := pure (expr.lam n bi) <*> pure y <*> g [⟨n, bi, y⟩] b
| (coord.pi_var_type)     (expr.pi   n bi y   b) := pure (expr.pi n bi)  <*> g [] y <*> pure b
| (coord.pi_body)         (expr.pi   n bi y   b) := pure (expr.pi n bi)  <*> pure y <*> g [⟨n, bi, y⟩] b
| (coord.elet_var_type)   (expr.elet n    y a b) := pure (expr.elet n)   <*> g [] a <*> pure a <*> pure b
| (coord.elet_assignment) (expr.elet n    y a b) := pure (expr.elet n)   <*> pure y <*> g [] a <*> pure b
| (coord.elet_body)       (expr.elet n    y a b) := pure (expr.elet n)   <*> pure y <*> pure a <*> g [⟨n,binder_info.default,y⟩] b
| _                       _                      := failure

/-- Returns the subexpression, if any, at the position given by the coordinate argument. -/
meta def expr.coord.follow : coord → expr → option expr
| c e :=
    let r := (@except_t.run (option expr) id expr (expr.coord.modify (λ Γ e, throw e) c e)) in
    none <| except.to_option $ except.flip $ r

meta def expr.address.follow : address → expr → option expr
| (c :: rest) e := expr.coord.follow c e >>= expr.address.follow rest
| [] e := pure e

meta def expr.address.modify_core {t} [alternative t] (g : list binder → expr → t expr) : list binder → address → expr → t expr
| bs []     e := g bs e
| bs (h::t) e := expr.coord.modify (λ bs' s, expr.address.modify_core (bs' ++ bs) t s) h e

meta def expr.address.modify {t} [alternative t] (g : list binder → expr → t expr) : address → expr → t expr :=
expr.address.modify_core g []

/-- expr.replace r a o will replace the subexpression of `o` at position `a` with `r`. If `a` is not a valid address it will return `none`. -/
meta def expr.replace : expr → address → expr → option expr
| r := expr.address.modify (λ _ _, some r)

namespace zipper
    namespace path
        /-- An item in a zipper path. See  -/
        @[derive decidable_eq]
        meta inductive entry
        |app_fn          (fn : unit) (arg : expr) : entry
        |app_arg         (fn : expr) (arg : unit) : entry
        |lam_var_type    (var_name : name) (bi : binder_info) (var_type : unit) (body : expr) : entry
        |lam_body        (var_name : name) (bi : binder_info) (var_type : expr) (body : unit) : entry
        |pi_var_type     (var_name : name) (bi : binder_info) (var_type : unit) (body : expr) : entry
        |pi_body         (var_name : name) (bi : binder_info) (var_type : expr) (body : unit) : entry
        |elet_var_type   (var_name : name) (type : unit) (assignment : expr)    (body : expr) : entry
        |elet_assignment (var_name : name) (type : expr) (assignment : unit)    (body : expr) : entry
        |elet_body       (var_name : name) (type : expr) (assignment : expr)    (body : unit) : entry
    end path
    /-- A path is the part of the zipper that remembers the stuff above the zipper's cursor.-/
    @[inline] meta def path := list expr.zipper.path.entry

    namespace path

        open entry

        meta def entry.to_coord : path.entry → coord
        |(entry.app_fn _ _)        := coord.app_fn
        |(entry.app_arg _ _)       := coord.app_arg
        |(lam_var_type _ _ _ _)    := coord.lam_var_type
        |(lam_body _ _ _ _)        := coord.lam_body
        |(pi_var_type _ _ _ _)     := coord.pi_var_type
        |(pi_body _ _ _ _)         := coord.pi_body
        |(elet_var_type   _ _ _ _) := coord.elet_var_type
        |(elet_assignment _ _ _ _) := coord.elet_assignment
        |(elet_body       _ _ _ _) := coord.elet_body

        meta def to_address : path → address :=
        list.map entry.to_coord ∘ list.reverse

        open tactic

        meta def entry.to_tactic_format : path.entry → tactic format
        |(entry.app_fn  l r)         := (pure $ λ l r, l ++ " $ " ++ r) <*> pp l <*> pp r
        |(entry.app_arg l r)         := (pure $ λ l r, l ++ " $ " ++ r) <*> pp l <*> pp r
        |(lam_var_type    n _ y   b) := (pure $ λ n y   b, "λ "   ++ n ++ " : " ++ y ++ ", " ++ b) <*> pp n <*> pp y <*> pp b
        |(lam_body        n _ y   b) := (pure $ λ n y   b, "λ "   ++ n ++ " : " ++ y ++ ", " ++ b) <*> pp n <*> pp y <*> pp b
        |(pi_var_type     n _ y   b) := (pure $ λ n y   b, "Π "   ++ n ++ " : " ++ y ++ ", " ++ b) <*> pp n <*> pp y <*> pp b
        |(pi_body         n _ y   b) := (pure $ λ n y   b, "Π "   ++ n ++ " : " ++ y ++ ", " ++ b) <*> pp n <*> pp y <*> pp b
        |(elet_var_type   n   y a b) := (pure $ λ n y a b, "let " ++ n ++ " : " ++ y ++ " := " ++ a ++ " in " ++ b) <*> pp n <*> pp y <*> pp a <*> pp b
        |(elet_assignment n   y a b) := (pure $ λ n y a b, "let " ++ n ++ " : " ++ y ++ " := " ++ a ++ " in " ++ b) <*> pp n <*> pp y <*> pp a <*> pp b
        |(elet_body       n   y a b) := (pure $ λ n y a b, "let " ++ n ++ " : " ++ y ++ " := " ++ a ++ " in " ++ b) <*> pp n <*> pp y <*> pp a <*> pp b

        meta instance entry.has_to_tactic_format : has_to_tactic_format path.entry := ⟨entry.to_tactic_format⟩

        meta def entry.replace (f : ℕ → expr → expr) : ℕ → path.entry → path.entry
        |d (entry.app_fn  () r)          := (entry.app_fn  () (f d r))
        |d (entry.app_arg l ())          := (entry.app_arg (f d l) ())
        |d (lam_var_type    n bi ()   b)  := (lam_var_type    n bi ()  (f (d+1) b))
        |d (lam_body        n bi y   ())  := (lam_body        n bi (f d y)   ())
        |d (pi_var_type     n bi ()   b)  := (pi_var_type     n bi ()   (f (d+1) b))
        |d (pi_body         n bi y   ())  := (pi_body         n bi (f d y)   ())
        |d (elet_var_type   n    y a b)  := (elet_var_type   n    () (f d a) (f (d+1) b))
        |d (elet_assignment n    y a b)  := (elet_assignment n    (f d y) () (f (d+1) b))
        |d (elet_body       n    y a b)  := (elet_body       n    (f d y) (f d a) ())

        meta def entry.up : expr → entry → expr
        | x (entry.app_fn  () a)       := expr.app x a
        | x (entry.app_arg f  ())      := expr.app f x
        | x (lam_var_type   n bi _ b)  := expr.lam n bi x b
        | x (lam_body       n bi y _)  := expr.lam n bi y x
        | x (pi_var_type    n bi _ b)  := expr.pi  n bi x b
        | x (pi_body        n bi y _)  := expr.pi  n bi y x
        | x (elet_var_type   n _ a b)  := expr.elet n x a b
        | x (elet_assignment n t _ b)  := expr.elet n t x b
        | x (elet_body       n t a _)  := expr.elet n t a x

        meta def up : path → expr → expr
        | [] e := e
        | (h::t) e := up t $ entry.up e h

        meta instance : has_emptyc path := ⟨[]⟩

        meta def entry.down : coord → expr → option (entry × expr)
        |(coord.app_fn)          (expr.app f a)      := some ⟨entry.app_fn  () a       , f⟩
        |(coord.app_arg)         (expr.app f a)      := some ⟨entry.app_arg f ()       , a⟩
        |(coord.lam_var_type)    (expr.lam n bi y b) := some ⟨lam_var_type n bi () b   , y⟩
        |(coord.lam_body)        (expr.lam n bi y b) := some ⟨lam_body     n bi y ()   , b⟩
        |(coord.pi_var_type)     (expr.pi n bi y b ) := some ⟨pi_var_type  n bi () b   , y⟩
        |(coord.pi_body)         (expr.pi n bi y b ) := some ⟨pi_body      n bi y ()   , b⟩
        |(coord.elet_var_type)   (expr.elet n y a b) := some ⟨elet_var_type   n () a b , y⟩
        |(coord.elet_assignment) (expr.elet n y a b) := some ⟨elet_assignment n y () b , a⟩
        |(coord.elet_body)       (expr.elet n y a b) := some ⟨elet_body       n y a () , b⟩
        |_ _ := none

        meta def entry.as_binder : path.entry → option binder
        |(lam_body  n bi y   b) := some $ binder.mk n bi y
        |(pi_body   n bi y   b) := some $ binder.mk n bi y
        |(elet_body n    y a b) := some $ binder.mk n binder_info.default y
        |_ := none

        meta def entry.binder_depth : path.entry → nat
        | e := if option.is_some $ entry.as_binder e then 1 else 0

        meta def get_context : path → telescope :=
        list.filter_map entry.as_binder

        meta def binder_depth : path → ℕ :=
        list.sum ∘ list.map entry.binder_depth

        meta def replace (f : ℕ → expr → expr) : path → path
        | (pe::p) := entry.replace f (path.binder_depth p) pe :: replace p
        | [] := []

        meta def instantiate_vars : list expr → path → path
        | vs p := p.replace (λ d e, expr.instantiate_vars e ((list.map expr.var $ list.range d) ++ (vs.map (λ v, expr.lift_vars v 0 d))))

        meta def instantiate_nth : ℕ → expr → path → path
        | n a p := path.replace (λ d e, expr.instantiate_nth_var (n + d) (expr.lift_vars a 0 d) e) p
        -- /-- `as_subpath a b` finds the path `c` such that `b ++ c = a`. -/
        -- meta def as_subpath : path → path → option path := list.as_sublist
        meta def empty : path := []

        meta instance path_eq : decidable_eq path := list.decidable_eq

        meta def entry.mmap_exprs {t : Type → Type} [monad t] (f : telescope → expr → t expr) : telescope → expr → path.entry → t path.entry
        | Γ x (entry.app_fn  () r)           := pure entry.app_fn        <*>  pure () <*> (f Γ r)
        | Γ x (entry.app_arg l ())           := pure entry.app_arg       <*> (f Γ l)  <*> pure ()
        | Γ x (lam_var_type    n bi ()   b)  := pure (lam_var_type n bi) <*>  pure () <*> (f (⟨n, bi, x⟩::Γ) b)
        | Γ x (lam_body        n bi y   ())  := pure (lam_body     n bi) <*> (f Γ y)  <*>  pure ()
        | Γ x (pi_var_type     n bi ()   b)  := pure (pi_var_type  n bi) <*>  pure () <*> (f (⟨n,bi,x⟩::Γ) b)
        | Γ x (pi_body         n bi y   ())  := pure (pi_body      n bi) <*> (f Γ y)  <*>  pure ()
        | Γ x (elet_var_type   n    y a b)   := pure (elet_var_type   n) <*> pure ()  <*> (f Γ a)  <*> (f (⟨n,binder_info.default,x⟩::Γ) b)
        | Γ x (elet_assignment n    y a b)   := pure (elet_assignment n) <*> (f Γ y)  <*> pure ()  <*> (f (⟨n,binder_info.default,y⟩::Γ) b)
        | Γ x (elet_body       n    y a b)   := pure (elet_body       n) <*> (f Γ y)  <*> (f Γ a)  <*> pure ()

        meta def mmap_exprs {t : Type → Type} [m : monad t] (f : telescope → expr → t expr) : telescope → expr → path → t path
        | Γ x [] := pure []
        | Γ x (e :: p) := do
          e ← (@entry.mmap_exprs t m f (get_context p ++ Γ) x e),
          p ← mmap_exprs Γ (e.up x) p,
          pure $ e :: p
    end path
end zipper
/--
A zipper over expressions.
It does not replace bound variables with local constants, but instead maintains its own implicit context of the binders that it is under using its path.
Reference: [Functional Pearl - The Zipper](https://www.st.cs.uni-saarland.de/edu/seminare/2005/advanced-fp/docs/huet-zipper.pdf)
 -/
@[derive decidable_eq]
meta structure zipper :=
(get_path : zipper.path)
(cursor : expr)

/-- Result type of calling `zipper.down`.  -/
@[derive decidable_eq]
meta inductive down_result
|terminal : down_result
|app  (left : zipper) (right : zipper) : down_result
| lam (var_name : name) (bi : binder_info) (var_type : zipper) (body : zipper) : down_result
|  pi (var_name : name) (bi : binder_info) (var_type : zipper) (body : zipper) : down_result
|elet (var_name : name) (type : zipper) (assignment : zipper) (body : zipper) : down_result

meta def down_result.children_with_depth : down_result → list (zipper × nat)
|(down_result.terminal) := []
|(down_result.app l r) := [(l,0),(r,0)]
|(down_result.lam n bi vt b) := [(vt,0),(b,1)]
|(down_result.pi n bi vt b) := [(vt,0),(b,1)]
|(down_result.elet n t a b) := [(t,0),(a,0),(b,1)]

meta def down_result.children : down_result → list zipper :=
list.map prod.fst ∘ down_result.children_with_depth

namespace zipper
    open path path.entry
    meta def mmap_children {t : Type → Type} [monad t] (f : telescope → expr → t expr) : telescope → zipper → t zipper
    | Γ ⟨p,c⟩ := pure zipper.mk <*> path.mmap_exprs f Γ c p <*> f (get_context p ++ Γ) c
    meta instance : assignable zipper := ⟨@mmap_children⟩
    meta def of_path : path → expr → zipper := zipper.mk
    /-- Move the cursor down the expression tree.-/
    meta def down : zipper → down_result
    |⟨p, expr.app f a⟩ :=
        down_result.app
            ⟨entry.app_fn  () a  :: p, f⟩
            ⟨entry.app_arg f  () :: p, a⟩
    |⟨p, expr.lam n bi y b⟩ :=
        down_result.lam n bi
            ⟨lam_var_type n bi () b  :: p, y⟩
            ⟨lam_body     n bi y  () :: p, b⟩
    |⟨p, expr.pi  n bi y b⟩ :=
        down_result.pi n bi
            ⟨pi_var_type  n bi () b  :: p, y⟩
            ⟨pi_body      n bi y  () :: p, b⟩
    |⟨p, expr.elet n t a b⟩ :=
        down_result.elet n
            ⟨elet_var_type   n () a b :: p, t⟩
            ⟨elet_assignment n t () b :: p, a⟩
            ⟨elet_body       n t a () :: p, b⟩
    |⟨p,e⟩ := down_result.terminal

    meta def children_with_depths : zipper → list (zipper × nat) :=
    down_result.children_with_depth ∘ down

    meta def children : zipper → list zipper :=
    down_result.children ∘ down

    meta def down_coord : coord → zipper → option zipper
    | c ⟨p, x⟩ := path.entry.down c x >>= (λ ⟨e,x⟩, some ⟨e::p, x⟩)

    /-- Pop the cursor up the expression tree. If we are already at the top, returns `none`. -/
    meta def up : zipper → option zipper
    |⟨[], e⟩ := none
    |⟨e :: p, c⟩ := some $ zipper.mk p $ path.entry.up c e

    meta def is_top : zipper → bool := option.is_none ∘ up

    meta def top : zipper → zipper | z := option.rec_on (up z) z top

    meta def down_app_fn  : zipper → option zipper := down_coord coord.app_fn

    meta def down_app_arg : zipper → option zipper := down_coord coord.app_arg

    /-- If the cursor is a binder, move the cursor to the binder's body. -/
    meta def down_body : zipper → option zipper := λ z,
        (down_coord coord.lam_body  z) <|>
        (down_coord coord.pi_body   z) <|>
        (down_coord coord.elet_body z)

    /-- If the cursor is a binder then move the cursor on to the binder's tyoe. -/
    meta def down_var_type : zipper → option zipper := λ z,
        (down_coord coord.lam_var_type  z) <|>
        (down_coord coord.pi_var_type   z) <|>
        (down_coord coord.elet_var_type z)

    /-- Move the cursor down according to the given address.
    If the zipper has the wrong structure then return none.-/
    meta def down_address : address → zipper → option zipper
    |[]     z := some z
    |(h::t) z := down_coord h z >>= down_address t

    meta def unzip : zipper → expr
    | z := option.rec_on (up z) (cursor z) (unzip)

    meta def zip : expr → zipper := zipper.mk []

    meta instance : has_coe expr zipper := ⟨zip⟩

    meta def set_cursor : expr → zipper → zipper
    |e ⟨p,_⟩ := ⟨p,e⟩

    /-- Map the cursor. -/
    meta def map : (expr → expr) → zipper → zipper
    |f ⟨p,e⟩ := ⟨p,f e⟩

    variables {T: Type → Type} [monad T]

    /-- Monad-map the cursor. -/
    meta def mmap : (expr → T expr) → zipper → T zipper
    |f ⟨p,e⟩ := zipper.mk p <$> f e

    meta def fold {α} (f : α → zipper → α) : α → zipper → α
    | a z := z.children.foldl fold $ f a z

    meta def mfold {α} (f : α → zipper → T α) : α → zipper → T α
    | a z := do a ← f a z, z.children.mfoldl mfold a

    meta def mfold_up {α} (f : α → zipper → T α) : α → zipper → T α
    | a z := f a z >>= λ a, option.rec_on (up z) (pure a) (mfold_up a)

    /-- Fold over each subzipper but if the monad fails then keep the α and don't recurse. -/
    meta def altfold [alternative T] {α} (f : α → zipper → T α) : α → zipper → T α
    | a z := (do a ← f a z, z.children.mfoldl altfold a) <|> pure a

    meta def altfold_up [alternative T] {α} (f : α → zipper → T α) : α → zipper → T α
    | a z := (f a z >>= λ a, option.rec_on (up z) (pure a) (altfold_up a)) <|> pure a

    meta def pick_up [alternative T] {α} (f : zipper → T α) : zipper → T α
    | z := f z <|> option.rec_on (up z) failure pick_up

    meta def get_address : zipper → address := to_address ∘ get_path

    /-- Get the context of the cursor. The first item in the list is the
    deepest (and therefore associated with the 0th de-Bruijn variable) -/
    meta def get_context : zipper → telescope := path.get_context ∘ get_path

    /-- The number of binders above the cursor. -/
    meta def binder_depth : zipper → ℕ := list.length ∘ get_context

    /-- Replace the cursor and unzip. -/
    meta def unzip_with : expr → zipper → expr := λ e z, unzip $ z.set_cursor e

    meta def is_var : zipper → bool := expr.is_var ∘ cursor

    meta def is_constant : zipper → bool := expr.is_constant ∘ cursor

    /-- True when the cursor does not contain local constants. -/
    meta def has_local : zipper → bool | z := z.cursor.has_local

    /-- True when the cursor is on a local constant. -/
    meta def is_local_constant : zipper → bool :=
    expr.is_local_constant ∘ cursor

    /-- True when the cursor is on a metavariable. -/
    meta def is_mvar : zipper → bool
    | z := match z.cursor with (expr.mvar _ _ _) := tt | _ := ff end

    /-- True when the cursor has no further recursive arguments. -/
    meta def is_terminal : zipper → bool :=
    λ z, z.down = down_result.terminal

    /-- True when the cursor is _in_ the arg of an app.
    That is, the path directly above is `app_arg`. -/
    meta def is_app_arg : zipper → bool
    |⟨(entry.app_arg _ _)::t,_⟩ := tt |_ := ff

    /-- Make fresh local_constants for each item in the
    context and instantiate the cursor with them. -/
    meta def instantiate_cursor : zipper → tactic (expr × list expr)
    | z := do hs ← telescope.to_locals z.get_context, pure (instantiate_vars z.cursor hs, hs)

    /-- Infer the type of the subexpression at the cursor position. -/
    meta def infer_type : zipper → tactic expr := λ z, do
        (c,_) ← instantiate_cursor z,
        tactic.infer_type c

    meta instance : has_to_tactic_format zipper := ⟨λ z, do
        whole  ← tactic.pp $ z.unzip_with (expr.const `O []),
        cursor ← tactic.pp z.cursor,
        pure $ format.highlight cursor format.color.blue ++ " in " ++ whole⟩

    meta def instantiate_mvars : zipper → tactic zipper | z := do
        e ← tactic.instantiate_mvars (unzip z),
        down_address (get_address z) (zip e)

    meta def instantiate_vars : zipper → list expr → zipper
    | z vs := option.rec (undefined_core "instantiate_vars unreachable") id
              $ down_address (get_address z)
              $ zip
              $ expr.instantiate_vars z.unzip vs

    /-- Check if the paths of the given zippers are equal.
    That is, they are the same except for the cursor expressions. -/
    meta def above_equal : zipper → zipper → bool
    |⟨p₁,_⟩ ⟨p₂,_⟩ := p₁ = p₂

    meta def address_below : zipper → zipper → option address
    | z₁ z₂ := address.as_below z₁.get_address z₂.get_address

    meta def path.apply : path → expr → expr | p e := zipper.unzip ⟨p,e⟩

    protected meta def lt : zipper → zipper → bool
    | z₁ z₂ := bor (z₁.get_address < z₂.get_address)
               $ band (z₁.get_address = z₂.get_address)
               $ z₁.unzip < z₂.unzip

    meta instance : has_lt zipper :=
    ⟨λ z₁ z₂, zipper.lt z₁ z₂⟩

    meta instance : decidable_rel ((<) : zipper → zipper → Prop) := by apply_instance

    /-- Find all zippers whose cursor is on the given de Bruijn variable. -/
    meta def find_var : zipper → ℕ → list zipper
    | z n := match z.cursor with
      | (expr.var i) :=
        if n + z.binder_depth = i then [z] else []
      | c :=
        if expr.get_free_var_range c < n + z.binder_depth then [] else
        z.children.bind (λ z, find_var z n)
      end

    meta def to_path : address → expr → option zipper.path
    | a e := zipper.get_path <$> zipper.down_address a (zipper.zip e)
end zipper


end expr
