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


inductive Beta : Lam → Lam → Prop where
  | red m n : Beta (Lam.app (Lam.abs m) n) (m.subst_free 0 (n.inc) |>.dec)
  | appl m n k : Beta m n → Beta (Lam.app m k) (Lam.app n k)
  | appr m n k : Beta m n → Beta (Lam.app k m) (Lam.app k n)
  | abs m n : Beta m n → Beta (Lam.abs m) (Lam.abs n)

infixr:80 " →β " => Beta

@[simp]
lemma Beta.var : (Lam.var x) →β M → False := by
  intro h
  cases h

lemma Beta.abs_iff : (Lam.abs m) →β M ↔ ∃ n, M = Lam.abs n ∧ m →β n := by
  apply Iff.intro
  . intro h1
    cases h1
    rename Lam => n
    use n
  . intro ⟨n, h⟩
    rw [h.1]
    apply Beta.abs _ _ h.2

lemma Beta.abs_congr : (Lam.abs m) →β (Lam.abs n) ↔ m →β n := by
  apply Iff.intro
  . intro h
    cases h
    assumption
  . apply Beta.abs

-- should finite closure?
inductive Betas : Lam → Lam → Type where
  | refl : Betas m m
  | red : m →β n → Betas m n
  | trans : Betas m n → Betas n k → Betas m k

infixr:80 " ↠β " => Betas

-- theorem Beta.confluence : M →β N → M →β N' → ∃ K, N →β K ∧ N' →β K := by
--   intro h1 h2
--   cases h1 with
--   | appl m n k h => sorry
--   | appr m n k h => sorry
--   | abs m n h => sorry
--   | red m n => sorry

end Lam
#check Prod
