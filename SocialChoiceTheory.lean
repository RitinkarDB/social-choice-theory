-- This module serves as the root of the `SocialChoiceTheory` library.
-- Import modules here that should be built as part of the library.
import SocialChoiceTheory.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic

/-!
# Arrow’s Impossibility and Gibbard–Satterthwaite in Lean 4

Using the definitions of `Basic.lean`, we formalize profiles, social choice functions,
and social welfare functions, plus the core definitions and statements from Reny’s paper.
-/

namespace Choice

variable {X : Type u} [Fintype X] [DecidableEq X] {n : ℕ}

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

/-- Theorem A (Muller–Satterthwaite): Pareto + Monotonicity ⇒ Dictatorship. -/
theorem Muller_Satterthwaite
  (f : SCF X n)
  (hPE : ParetoEfficient_SCF f)
  (hMono : Monotonic f) :
  Dictatorial_SCF f := by
  -- proof omitted
  sorry

/-- Theorem B (Arrow): Pareto + IIA ⇒ Dictatorship. -/
theorem Arrow_Impossibility
  (F : SWF X n)
  (hPE : ParetoEfficient_SWF F)
  (hIIA : IIA F) :
  Dictatorial_SWF F := by
  -- proof omitted
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
  -- proof omitted
  sorry

end Choice
