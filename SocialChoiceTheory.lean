-- This module serves as the root of the `SocialChoiceTheory` library.
-- Import modules here that should be built as part of the library.
import SocialChoiceTheory.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic

/-!
# Arrow’s Impossibility and Gibbard–Satterthwaite in Lean 4

Based off Reny (2001)
-/

namespace Choice

variable {X : Type u} [Fintype X] [DecidableEq X] {n : ℕ}

variable {X : Type u} {n : ℕ}

/-- A social choice function selects a single alternative given a profile. -/
abbrev SCF : Type u := Profile X n → X

/-! ## Preference & Profiles -/

/-- A (strict) ranking is a strict linear order on `X`. -/
def is_strict_linear_order (r : X → X → Prop) : Prop :=
  Irreflexive r ∧ Transitive r ∧ ∀ a b : X, a ≠ b → r a b ∨ r b a

/-- A (weak) ranking is a complete preorder on `X`. -/
def is_weak_linear_order (r : X → X → Prop) : Prop :=
  Reflexive r ∧ Transitive r ∧ ∀ a b : X, r a b ∨ r b a

/-- A profile of individual strict rankings. -/
def StrictProfile :=
  { p : Profile X n // ∀ i, is_strict_linear_order (p.preferences i) }

/-! ## Social Choice Functions -/

/-- A social choice function selects a single alternative given a profile. -/
abbrev SCF (X : Type u) (n : ℕ) : Type u := Profile X n → X

/-- “`a` is top-ranked in a strict order `r`.” -/
def is_top (r : X → X → Prop) (a : X) : Prop :=
  ∀ b, b ≠ a → r a b

/-- “`b` is bottom‐ranked in a strict order `r`.” -/
def is_bottom (r : X → X → Prop) (b : X) : Prop :=
  ∀ a, a ≠ b → r a b


/-- Pareto efficiency: if everybody ranks `a` first, society picks `a`. -/
def ParetoEfficient_SCF (f : SCF X n) : Prop :=
  ∀ p a, (∀ i, is_top (p.preferences i) a) → f p = a

/-- Monotonicity: improving the chosen alternative never makes it lose. -/
def Monotonic (f : SCF X n) : Prop :=
  ∀ p q a,
    f p = a →
    (∀ i b, p.preferences i a b → q.preferences i a b) →
    f q = a

/-- Dictatorial: there is `i` whose top always prevails. -/
def Dictatorial_SCF (f : SCF X n) : Prop :=
  ∃ i, ∀ p a, f p = a ↔ is_top (p.preferences i) a

  /-- Raise `b` immediately above `a` in voter `i`’s ranking. -/
def raiseAboveOne (i : Fin n) (p : Profile X n) (a b : X) : Profile X n :=
  { preferences := fun j =>
      if j = i then
        fun x y =>
          if x = b ∧ y = a then True
          else if x = a ∧ y = b then False
          else p.preferences j x y
      else
        p.preferences j }

/-- Sequence of profiles raising `b` above `a` in the first `k` individuals. -/
def raiseSeq (p : Profile X n) (a b : X) : Fin (n+1) → Profile X n
| ⟨0, _⟩ => p
| ⟨m+1, h⟩ =>
  let i : Fin n := ⟨m, Nat.lt_of_succ_lt_succ h⟩
  let prev := raiseSeq p a b ⟨m, Nat.lt_succ_of_lt (Nat.lt_of_succ_lt_succ h)⟩
  raiseAboveOne i prev a b



/-! ## Social Welfare Functions -/

/-- Pareto efficiency: unanimous individual `a ≻ b` implies `a ≻ b` socially. -/
def ParetoEfficient_SWF (F : SWF X n) : Prop :=
  ∀ p a b, (∀ i, p.preferences i a b) → F p a b

/-- Independence of irrelevant alternatives: pairwise social ranking depends only on pairwise inputs. -/
def IIA (F : SWF X n) : Prop :=
  ∀ p q a b,
    (∀ i, p.preferences i a b ↔ q.preferences i a b) →
    (F p a b ↔ F q a b)

/-- Dictatorial: one individual’s ordering always imposes itself. -/
def Dictatorial_SWF (F : SWF X n) : Prop :=
  ∃ i, ∀ p a b, p.preferences i a b → F p a b

/-! ## Main Theorems (statements only) -/

universe u

variable {X : Type u} {n : ℕ}




/-- Step 1 (pivot lemma): there is some index `k` where the social choice switches from `a` to `b`. -/
theorem exists_pivot
  (f : SCF)
  (hPE : ParetoEfficient f)
  (hM  : Monotonic f)
  {a b : X} (hab : a ≠ b)
  (p : Profile X n)
  (h_top : ∀ i, is_top (p.preferences i) a)
  (h_bot : ∀ i, is_bottom (p.preferences i) b) :
  ∃ k : Fin (n+1),
    -- at k = 0, everyone ranks a top ⇒ f = a
    f (raiseSeq p a b ⟨0, by simp⟩) = a ∧
    -- at k = n, everyone ranks b top ⇒ f = b
    f (raiseSeq p a b ⟨n, by simp⟩) = b := by
  -- witness k = n
  let k_fin : Fin (n+1) := ⟨n, Nat.lt_succ_self n⟩
  use k_fin
  constructor
  · -- at 0: Pareto yields f p = a
    exact hPE p a h_top
  · -- at n: after raising for all, b is top for everyone ⇒ f = b
    have hb_top : ∀ i, is_top (raiseSeq p a b k_fin).preferences i b := by intro _; trivial
    exact hPE _ _ hb_top


/-- Theorem A (Muller–Satterthwaite): Pareto + Monotonicity ⇒ Dictatorship. -/
theorem Muller_Satterthwaite
  (f : SCF X n)
  (hPE : ParetoEfficient_SCF f)
  (hMono : Monotonic f) :
  Dictatorial_SCF f := by
  sorry



/-- Theorem B (Arrow): Pareto + IIA ⇒ Dictatorship. -/
theorem Arrow_Impossibility
  (F : SWF X n)
  (hPE : ParetoEfficient_SWF F)
  (hIIA : IIA F) :
  Dictatorial_SWF F := by
  -- proof TODO
  sorry

/-- Proposition (Muller–Satterthwaite link): Strategy-proof + Onto ⇒ Pareto + Monotonic. -/
-- (cf. Muller & Satterthwaite 1977)
def Onto (f : SCF X n) : Prop :=
  ∀ a, ∃ p, f p = a

/-- Strategy‑proofness: no individual can gain by misreporting. -/
def StrategyProof (f : SCF X n) : Prop :=
  ∀ p i p',
    (∀ j, j ≠ i → p'.preferences j = p.preferences j) →
    f p = f p' →
    -- chosen outcome under `p` is at least as good in `p i` as under `p'`
    is_top (p.preferences i) (f p)

/-- Corollary (Gibbard–Satterthwaite). -/
theorem Gibbard_Satterthwaite
  (f : SCF X n)
  (hStrat : StrategyProof f)
  (hOnto : Onto f)
  (hℓ : Fintype.card X ≥ 3) :
  Dictatorial_SCF f := by
  -- proof TODO
  sorry

end Choice
