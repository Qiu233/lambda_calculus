import Mathlib

-- System F, also known as λ2, supports parametric polymorphism

/--set of variable symbols-/
inductive V
/--set of type variable symbols-/
inductive TV
instance : DecidableEq TV := by
  intro x y
  cases x
/--set of well-formed types-/
inductive T where
  | type : TV → T
  | func : T → T → T
  | forall_ : TV → T → T
instance : Coe TV T := ⟨T.type⟩
def T.subst (t : T) (v : TV) (t' : T) : T :=
  match t with
  | type x =>
    if x = v
      then t'
      else t
  | func α β =>
    func (α.subst v t') (β.subst v t')
  | forall_ x α =>
    if x = v
      then t
      else forall_ x (α.subst v t')
/--set of well-formed terms-/
inductive Lam where
  | var : V → Lam
  | app : Lam → Lam → Lam
  | app₂ : Lam → T → Lam
  | abst : V → T → Lam → Lam
  | abst₂ : TV → Lam → Lam
instance : Coe V Lam := ⟨Lam.var⟩
/--Statements-/
structure S where
  term : Lam
  type : T
def S.mk' (v : V) (t : T) := S.mk (Lam.var v) t
/--Declarations-/
structure D extends S where
  mk' ::
  sub : V
  is_sub : term = Lam.var sub
def D.mk (v : V) (t : T) := D.mk' (S.mk (Lam.var v) t) v (by simp)

infix:100 " :; " => D.mk
infix:100 " :: " => S.mk
infixr:110 " →' " => T.func

declare_syntax_cat lambda_type_syntax
syntax ident : lambda_type_syntax
syntax "(" lambda_type_syntax ")" : lambda_type_syntax
syntax lambda_type_syntax " → " lambda_type_syntax : lambda_type_syntax
syntax " Π " ident ":" "*" "," lambda_type_syntax : lambda_type_syntax
syntax "𝓣[" lambda_type_syntax "]" : term


declare_syntax_cat lambda_syntax
syntax ident : lambda_syntax
syntax:100 lambda_syntax:100 lambda_syntax:101 : lambda_syntax
syntax:100 lambda_syntax:100 "[" lambda_type_syntax:101 "]" : lambda_syntax
syntax " λ " ident " : " lambda_type_syntax " , " lambda_syntax : lambda_syntax
syntax " λ " ident " : " " * " " , " lambda_syntax : lambda_syntax
syntax "(" lambda_syntax ")" : lambda_syntax
syntax "λ[" lambda_syntax "]" : term

open Lean in
partial def type_syntax : TSyntax `lambda_type_syntax → Lean.MacroM (TSyntax `term)
  | `(lambda_type_syntax| $id:ident) => `($id)
  | `(lambda_type_syntax| $α:lambda_type_syntax → $β:lambda_type_syntax) => do
    let a ← type_syntax α
    let b ← type_syntax β
    `(T.func ($a) ($b))
  | `(lambda_type_syntax| Π $v:ident : * , $body:lambda_type_syntax) => do
    let b ← type_syntax body
    `(T.forall_ ($v) ($b))
  | `(lambda_type_syntax| ($s:lambda_type_syntax)) => type_syntax s
  | _ => Lean.Macro.throwUnsupported

macro_rules
| `(𝓣[ $t:lambda_type_syntax ]) => type_syntax t

macro_rules
| `(λ[$var:ident]) => `($var)
| `(λ[$f:lambda_syntax $x:lambda_syntax]) => `(Lam.app λ[$f] λ[$x])
| `(λ[λ $var:ident : * , $body:lambda_syntax]) => `(Lam.abst₂ $var λ[$body])
| `(λ[($e:lambda_syntax)]) => `(λ[$e])
| `(λ[λ $var:ident : $type:lambda_type_syntax , $body:lambda_syntax]) => do
  let t ← type_syntax type
  `(Lam.abst $var ($t) λ[$body])
| `(λ[$f:lambda_syntax [$type:lambda_type_syntax]]) => do
  let t ← type_syntax type
  `(Lam.app₂ λ[$f] ($t))

-- TODO: need an ordered set
-- Maybe List? But List is requiring for BEq
/--This type is exactly what the symbol `⊢` is defined to be.-/
inductive Derive : Set D → S → Prop where
  | var :
    (x :; A ∈ Γ) →
    Derive Γ (x :: A)
  | app :
    Derive Γ (f :: A →' B) →
    Derive Γ (a :: A) →
    Derive Γ (λ[f a] :: B)
  | abst :
    Derive (Γ ∪ {x :; A}) (b :: B) →
    Derive Γ (λ[λ x : A, b] :: A →' B)
  | app₂ :
    Derive Γ (M :: T.forall_ α A) →
    Derive Γ (Lam.app₂ M B :: (A.subst α B))
  | abst₂ :
    Derive Γ (M :: A) →
    Derive Γ (Lam.abst₂ α M :: (T.forall_ α A))
-- TODO: do we really need `A:∗` judgement?

declare_syntax_cat derive_premise_syntax
syntax:30 "*" term : derive_premise_syntax
syntax:30 term : derive_premise_syntax
syntax:26 " # " derive_premise_syntax,* " ⊢ " term:26 : term
syntax:26 " # " "," derive_premise_syntax,* " ⊢ " term:26 : term

macro_rules
| `(#⊢ $conclusion:term) => `(Derive {} ($conclusion))
| `(# $basis ⊢ $conclusion:term) => do
  let initial ← match basis with
    | `(derive_premise_syntax| * $t:term) => `($t:term)
    | `(derive_premise_syntax| $t:term) => `($t:term)
    | _ => Lean.Macro.throwUnsupported
  `(Derive ($initial) ($conclusion))
| `(# $basis, $context,* ⊢ $conclusion:term) => do
  let wrap
    | `(derive_premise_syntax| * $t:term) => `($t:term)
    | `(derive_premise_syntax| $t:term) => `({$t:term})
    | _ => Lean.Macro.throwUnsupported
  let ts ← context.getElems.mapM wrap
  let initial ← match basis with
    | `(derive_premise_syntax| * $t:term) => `($t:term)
    | `(derive_premise_syntax| $t:term) => `($t:term)
    | _ => Lean.Macro.throwUnsupported
  let f a b := `(term| $a ∪ $b)
  `(Derive ($(← ts.foldlM f initial)) ($conclusion))
| `(# , $context,* ⊢ $conclusion:term) => do
  let wrap
    | `(derive_premise_syntax| * $t:term) => `($t:term)
    | `(derive_premise_syntax| $t:term) => `({$t:term})
    | _ => Lean.Macro.throwUnsupported
  let ts ← context.getElems.mapM wrap
  let initial ← `(term| {})
  let f a b := `(term| $a ∪ $b)
  `(Derive ($(← ts.foldlM f initial)) ($conclusion))


-- not sure what's making this proof works, there's issues to solve, see TODOs.
open Derive in
example : #⊢
    λ[λ α : *, λ f : (α → α), λ x : α, f (f x)] :: 𝓣[Π α : *, (α → α) → α → α]
    := by
  apply abst₂
  apply abst
  apply abst
  apply app
  . apply var
    simp
    apply Or.inr
    congr
  . apply app
    apply var
    simp
    apply Or.inr
    congr
    apply var
    simp
