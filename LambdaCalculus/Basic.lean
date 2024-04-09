import Mathlib

inductive Lam where
  | var : ℕ → Lam
  | app : Lam → Lam → Lam
  | abs : Lam → Lam


namespace Lam

def toString (wrap : Bool := false) : Lam → String
  | Lam.var x => ToString.toString x
  | Lam.abs m => -- s! "(λ {m.toString true})"
    match m, wrap with
    | Lam.abs _, true => s! "(λ {m.toString false})"
    | Lam.abs _, false => s! "λ {m.toString false}"
    | _, true => s! "(λ {m.toString true})"
    | _, false => s! "λ {m.toString true}"
  | Lam.app m (Lam.app n l) => s! "{m.toString true} ({(Lam.app n l).toString true})"
  | Lam.app m n => s! "{m.toString true} {n.toString true}"

instance : ToString Lam := ⟨Lam.toString false⟩

instance : OfNat Lam n where
  ofNat := Lam.var n

instance decEq : DecidableEq Lam
  | Lam.var x, Lam.var y =>
    if h : x = y
      then Decidable.isTrue (by simp [h])
      else Decidable.isFalse (by simp [h])
  | Lam.app m n, Lam.app m' n' =>
    match decEq m m', decEq n n' with
    | Decidable.isTrue h1, Decidable.isTrue h2 => Decidable.isTrue (by simp [h1, h2])
    | Decidable.isTrue h1, Decidable.isFalse h2 => Decidable.isFalse (by simp [h1, h2])
    | Decidable.isFalse h1, Decidable.isTrue h2 => Decidable.isFalse (by simp [h1, h2])
    | Decidable.isFalse h1, Decidable.isFalse h2 => Decidable.isFalse (by simp [h1, h2])
  | Lam.abs m, Lam.abs n =>
    match decEq m n with
    | Decidable.isTrue h => Decidable.isTrue (by simp [h])
    | Decidable.isFalse h => Decidable.isFalse (by simp [h])
  | Lam.var _, Lam.app _ _ => Decidable.isFalse (by simp)
  | Lam.var _, Lam.abs _ => Decidable.isFalse (by simp)
  | Lam.app _ _, Lam.var  _ => Decidable.isFalse (by simp)
  | Lam.app _ _, Lam.abs _ => Decidable.isFalse (by simp)
  | Lam.abs _, Lam.var _ => Decidable.isFalse (by simp)
  | Lam.abs _, Lam.app _ _ => Decidable.isFalse (by simp)

declare_syntax_cat lambda_calculus
syntax num : lambda_calculus
syntax:100 lambda_calculus:100 lambda_calculus:101 : lambda_calculus
syntax "λ" lambda_calculus : lambda_calculus
syntax "(" lambda_calculus ")" : lambda_calculus
syntax ident : lambda_calculus
syntax "λ[" lambda_calculus "]" : term

macro_rules
| `(λ[ $i:num ]) => `(Lam.var $i)
| `(λ[ $M:lambda_calculus $N:lambda_calculus ]) => `(Lam.app λ[$M] λ[$N])
| `(λ[ λ $M:lambda_calculus ]) => `(Lam.abs λ[$M])
| `(λ[ ($M:lambda_calculus) ]) => `(λ[$M])
| `(λ[ $n:ident ]) => pure n

#eval λ[(λ 1) 3]
#eval λ[(λ(λ1 0))1]
#eval λ[λ λ (λ(λ1 0))1]
#eval λ[λ λ ((λ2 0))]
#eval λ[((λ2 0))]


def inc : Lam → Lam := go 0 where
  go s
  | Lam.var x =>
    Lam.var (if x < s then x else (x + 1))
  | Lam.app m n => Lam.app (go s m) (go s n)
  | Lam.abs m => Lam.abs $ go (s + 1) m

def dec : Lam → Lam := go 0 where
  go s
  | Lam.var x =>
    Lam.var (if x < s then x else (x - 1))
  | Lam.app m n => Lam.app (go s m) (go s n)
  | Lam.abs m => Lam.abs $ go (s + 1) m

theorem dec_inc.go (m : Lam) : dec.go t (inc.go t m) = m := by
  match m with
  | Lam.var x =>
    simp [inc.go, dec.go]
    split
    . simp
    case inr h1 =>
      split
      case inl h2 =>
        simp at h1
        linarith only [h1, h2]
      case inr h2 =>
        simp
  | Lam.app m n =>
    simp [inc.go, dec.go]
    apply And.intro
    . apply dec_inc.go
    . apply dec_inc.go
  | Lam.abs n =>
    simp [inc.go, dec.go]
    apply dec_inc.go

@[simp]
theorem dec_inc : dec (inc m) = m := by
  cases m <;> simp [inc, inc.go, dec, dec.go, dec_inc.go]

def subst_free (M : Lam) (i : ℕ) (j : Lam) :=
  match M with
  | Lam.var x =>
    if x = i
      then j
      else M
  | Lam.app m n =>
    Lam.app (subst_free m i j) (subst_free n i j)
  | Lam.abs m =>
    Lam.abs (subst_free m (i + 1) (j.inc))



end Lam
