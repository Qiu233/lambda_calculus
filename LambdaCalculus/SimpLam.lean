import Mathlib
import Lean

-- Lean4's parameter command is absent,
-- and these two definitions will make code more consice than using variable command

/--set of variable symbols-/
inductive V
/--set of type variable symbols-/
inductive TV

/--set of well-formed types-/
inductive T where
  | type : TV → T
  | func : T → T → T
/--set of well-formed terms-/
inductive Lam where
  | var : V → Lam
  | app : Lam → Lam → Lam
  | abst : V → T → Lam → Lam
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

declare_syntax_cat lambda_syntax
syntax ident : lambda_syntax
syntax:100 lambda_syntax:100 lambda_syntax:101 : lambda_syntax
syntax " λ " ident " : " term " , " lambda_syntax : lambda_syntax
syntax "(" lambda_syntax ")" : lambda_syntax
syntax "λ[" lambda_syntax "]" : term

macro_rules
| `(λ[$var:ident]) => `($var)
| `(λ[$f:lambda_syntax $x:lambda_syntax]) => `(Lam.app λ[$f] λ[$x])
| `(λ[λ $var:ident : $type:term , $body:lambda_syntax]) => `(Lam.abst $var $type λ[$body])
| `(λ[($e:lambda_syntax)]) => `(λ[$e])

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

section
  variable {Γ : Set D} {A B : T} {f a b : Lam} {x : V}

  #check (Derive.var :
    x :; A ∈ Γ →
    #Γ ⊢ x :: A
    )
  #check (Derive.app :
    #Γ ⊢ f :: A →' B →
    #Γ ⊢ a :: A →
    #Γ ⊢ λ[f a] :: B
    )
  #check (Derive.abst :
    #Γ,x :; A ⊢ b :: B →
    #Γ        ⊢ λ[λ x : A, b] :: A →' B
    )
end

open Derive in
example : #⊢
    λ[λ y : (α →' β), λ z : α, y z] ::
    (α →' β) →' α →' β
    := by
  apply abst
  apply abst
  apply app
  . apply var
    apply Or.inl
    simp
    congr
  . apply var
    apply Or.inr
    simp
