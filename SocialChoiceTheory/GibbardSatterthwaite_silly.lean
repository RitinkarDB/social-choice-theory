import SocialChoiceTheory.Arrow
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

namespace SocialChoiceTheory

/-!
# Gibbard-Satterthwaite from Arrow

This file derives a strict-ballot version of Gibbard-Satterthwaite following
Nipkow's pair-top construction.
-/

section StrictBallots

variable {ι σ : Type*}
variable [Fintype ι] [DecidableEq ι] [DecidableEq σ]

/--
Strict linear ballots for the Gibbard-Satterthwaite side.

`lt x y` means "`y` is strictly preferred to `x`".
This matches Nipkow's orientation.
-/
structure LinBallot (σ : Type*) where
  lt : σ → σ → Prop
  irrefl : Irreflexive lt
  trans : Transitive lt
  total : ∀ ⦃x y : σ⦄, x ≠ y → lt x y ∨ lt y x

namespace LinBallot

/-- Weak order associated to a strict linear ballot. -/
def toPrefOrder (L : LinBallot σ) : PrefOrder σ where
  rel x y := x = y ∨ L.lt x y
  refl x := Or.inl rfl
  total x y := by
    by_cases h : x = y
    · exact Or.inl (Or.inl h)
    · rcases L.total h with hxy | hyx
      · exact Or.inl (Or.inr hxy)
      · exact Or.inr (Or.inr hyx)
  trans := by
    intro x y z hxy hyz
    rcases hxy with rfl | hxy
    · exact hyz
    · rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inr (L.trans hxy hyz)

lemma toPrefOrder_strict_iff (L : LinBallot σ) {x y : σ} :
    StrictPref (toPrefOrder L) x y ↔ L.lt x y := by
  constructor
  · intro h
    rcases h with ⟨hxy, hyx⟩
    rcases hxy with hEq | hlt
    · subst hEq
      exfalso
      exact hyx (Or.inl rfl)
    · exact hlt
  · intro h
    constructor
    · exact Or.inr h
    · intro hyx
      rcases hyx with hEq | hlt
      · subst hEq
        exact L.irrefl _ h
      · exact L.irrefl _ (L.trans h hlt)

lemma toPrefOrder_eq_or_lt (L : LinBallot σ) (x y : σ) :
    L.toPrefOrder x y ↔ x = y ∨ L.lt x y := by
  rfl

end LinBallot

/-- Profiles of strict ballots for the GS side. -/
abbrev SProfile (ι σ : Type*) := ι → LinBallot σ

/-- Resolute social choice functions on strict-ballot profiles. -/
abbrev SCF (ι σ : Type*) := SProfile ι σ → σ

def ChoosesFrom (g : SCF ι σ) (X : Finset σ) : Prop :=
  ∀ P, g P ∈ X

def OntoOn (g : SCF ι σ) (X : Finset σ) : Prop :=
  ∀ a, a ∈ X → ∃ P, g P = a

def sProfileUpdate (P : SProfile ι σ) (i : ι) (L : LinBallot σ) : SProfile ι σ :=
  fun j => if j = i then L else P j

def Manipulable (g : SCF ι σ) (X : Finset σ) : Prop :=
  ∃ P : SProfile ι σ, ∃ i : ι, ∃ L : LinBallot σ,
    let P' := sProfileUpdate P i L
    g P ∈ X ∧ g P' ∈ X ∧
    g P ≠ g P' ∧
    (P i).lt (g P) (g P')

def NonManipulable (g : SCF ι σ) (X : Finset σ) : Prop :=
  ¬ Manipulable g X

/--
Choice dictatorship on the strict-ballot side:
the chosen alternative is top-ranked by voter `i` among all alternatives in `X`.
-/
def IsChoiceDictatorship (g : SCF ι σ) (X : Finset σ) : Prop :=
  ∃ i : ι, ∀ P : SProfile ι σ, ∀ a : σ,
    a ∈ X → a ≠ g P → (P i).lt a (g P)

/-- Coerce a strict-ballot profile to the weak-order profile used by `SWF`. -/
def weakProfileOf (P : SProfile ι σ) : Profile ι σ :=
  fun i => (P i).toPrefOrder

end StrictBallots

section Top

variable {σ : Type*} [DecidableEq σ]

/--
Move every element of `S` to the top of the strict ballot, preserving
the relative order within `S` and within its complement.
-/
noncomputable def topifyLin (S : Finset σ) (L : LinBallot σ) : LinBallot σ where
  lt x y :=
    if x ∈ S then
      if y ∈ S then L.lt x y else False
    else
      if y ∈ S then True else L.lt x y
  irrefl := by
    intro x
    by_cases hx : x ∈ S <;> simp [hx, L.irrefl x]
  trans := by
    intro x y z
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · by_cases hz : z ∈ S
        · simp [hx, hy, hz]
          intro hxy hyz
          exact L.trans hxy hyz
        · simp [hx, hy, hz]
      · by_cases hz : z ∈ S
        · simp [hx, hy, hz]
        · simp [hx, hy, hz]
    · by_cases hy : y ∈ S
      · by_cases hz : z ∈ S
        · simp [hx, hy, hz]
        · simp [hx, hy, hz]
      · by_cases hz : z ∈ S
        · simp [hx, hy, hz]
        · simp [hx, hy, hz]
          intro hxy hyz
          exact L.trans hxy hyz
  total := by
    intro x y hxy
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · simp [hx, hy]
        exact L.total hxy
      · simp [hx, hy]
    · by_cases hy : y ∈ S
      · simp [hx, hy]
      · simp [hx, hy]
        exact L.total hxy

lemma topifyLin_mem_mem
    {S : Finset σ} {L : LinBallot σ} {x y : σ}
    (hx : x ∈ S) (hy : y ∈ S) :
    (topifyLin S L).lt x y ↔ L.lt x y := by
  simp [topifyLin, hx, hy]

lemma topifyLin_not_mem_not_mem
    {S : Finset σ} {L : LinBallot σ} {x y : σ}
    (hx : x ∉ S) (hy : y ∉ S) :
    (topifyLin S L).lt x y ↔ L.lt x y := by
  simp [topifyLin, hx, hy]

lemma topifyLin_not_mem_mem
    {S : Finset σ} {L : LinBallot σ} {x y : σ}
    (hx : x ∉ S) (hy : y ∈ S) :
    (topifyLin S L).lt x y := by
  simp [topifyLin, hx, hy]

lemma not_topifyLin_mem_not_mem
    {S : Finset σ} {L : LinBallot σ} {x y : σ}
    (hx : x ∈ S) (hy : y ∉ S) :
    ¬ (topifyLin S L).lt x y := by
  simp [topifyLin, hx, hy]

end Top

section TopProfile

variable {ι σ : Type*} [DecidableEq σ]

noncomputable def topProfile (S : Finset σ) (P : SProfile ι σ) : SProfile ι σ :=
  fun i => topifyLin S (P i)

lemma topProfile_apply
    (S : Finset σ) (P : SProfile ι σ) (i : ι) :
    topProfile S P i = topifyLin S (P i) := rfl

end TopProfile

section NonManipAndMonotonicity

variable {ι σ : Type*}
variable [Fintype ι] [DecidableEq ι] [DecidableEq σ]

lemma nonManipulable_iff
    (g : SCF ι σ) (X : Finset σ) :
    NonManipulable g X ↔
      ∀ P : SProfile ι σ, ∀ i : ι, ∀ L : LinBallot σ,
        let P' := sProfileUpdate P i L
        g P ∈ X → g P' ∈ X → g P ≠ g P' →
          (P i).lt (g P') (g P) ∧ L.lt (g P) (g P') := by
  classical
  constructor
  · intro hnm P i L
    dsimp
    intro hP hP' hneq
    constructor
    · by_contra hnot
      have htot := (P i).total hneq
      rcases htot with hleft | hright
      · exact hnm ⟨P, i, L, hP, hP', hneq, hleft⟩
      · exact hnot hright
    · by_contra hnot
      have hneq' : g (sProfileUpdate P i L) ≠ g P := by
        intro hEq
        apply hneq
        exact hEq.symm
      have htot := L.total hneq'
      rcases htot with hleft | hright
      · have hrestore : sProfileUpdate (sProfileUpdate P i L) i (P i) = P := by
          funext j
          by_cases hji : j = i
          · subst hji
            simp [sProfileUpdate]
          · simp [sProfileUpdate, hji]
        apply hnm
        refine ⟨sProfileUpdate P i L, i, P i, hP', ?_, ?_, ?_⟩
        · simpa [hrestore] using hP
        · simpa [hrestore] using hneq'
        · simpa [sProfileUpdate, hrestore] using hleft
      · exact hnot hright
  · intro h hman
    rcases hman with ⟨P, i, L, hP, hP', hneq, hlt⟩
    have hback := h P i L hP hP' hneq
    exact (P i).irrefl _ ((P i).trans hlt hback.1)

noncomputable def switchProfile
    [Fintype ι] [DecidableEq ι]
    (P P' : SProfile ι σ) (k : ℕ) : SProfile ι σ :=
  let e := Fintype.equivFin ι
  fun i =>
    if (e i : ℕ) < k then P' i else P i

lemma switchProfile_zero
    [Fintype ι] [DecidableEq ι]
    (P P' : SProfile ι σ) :
    switchProfile P P' 0 = P := by
  classical
  funext i
  simp [switchProfile]

lemma switchProfile_all
    [Fintype ι] [DecidableEq ι]
    (P P' : SProfile ι σ) :
    switchProfile P P' (Fintype.card ι) = P' := by
  classical
  funext i
  have hi : (Fintype.equivFin ι i : ℕ) < Fintype.card ι := by
    exact (Fintype.equivFin ι i).is_lt
  simp [switchProfile, hi]

lemma switchProfile_succ
    [Fintype ι] [DecidableEq ι]
    (P P' : SProfile ι σ) (k : ℕ)
    (hk : k < Fintype.card ι) :
    ∃ i : ι,
      switchProfile P P' (k + 1) =
        sProfileUpdate (switchProfile P P' k) i (P' i) := by
  classical
  let e := Fintype.equivFin ι
  let i : ι := e.symm ⟨k, hk⟩
  refine ⟨i, ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj
    have hi_eq : (e i : ℕ) = k := by
      simp [i, e]
    have hi_lt_succ : (e i : ℕ) < k + 1 := by
      rw [hi_eq]
      exact Nat.lt_succ_self k
    have hleft : switchProfile P P' (k + 1) i = P' i := by
      change (if (Fintype.equivFin ι i : ℕ) < k + 1 then P' i else P i) = P' i
      rw [if_pos hi_lt_succ]
    have hright : sProfileUpdate (switchProfile P P' k) i (P' i) i = P' i := by
      unfold sProfileUpdate
      simp
    rw [hleft, hright]
  · have hneNat : (e j : ℕ) ≠ k := by
      intro hej
      apply hj
      apply e.injective
      apply Fin.ext
      simpa [i, e] using hej
    have hright :
        sProfileUpdate (switchProfile P P' k) i (P' i) j = switchProfile P P' k j := by
      unfold sProfileUpdate
      simp [hj]
    by_cases hlt : (e j : ℕ) < k
    · have hlt_succ : (e j : ℕ) < k + 1 := Nat.lt_succ_of_lt hlt
      have hleft1 : switchProfile P P' (k + 1) j = P' j := by
        change (if (Fintype.equivFin ι j : ℕ) < k + 1 then P' j else P j) = P' j
        rw [if_pos hlt_succ]
      have hleft2 : switchProfile P P' k j = P' j := by
        change (if (Fintype.equivFin ι j : ℕ) < k then P' j else P j) = P' j
        rw [if_pos hlt]
      rw [hleft1, hright, hleft2]
    · have hnotlt' : ¬ ((e j : ℕ) < k + 1) := by
        intro h
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
        · exact hlt h'
        · exact hneNat h'
      have hleft1 : switchProfile P P' (k + 1) j = P j := by
        change (if (Fintype.equivFin ι j : ℕ) < k + 1 then P' j else P j) = P j
        rw [if_neg hnotlt']
      have hleft2 : switchProfile P P' k j = P j := by
        change (if (Fintype.equivFin ι j : ℕ) < k then P' j else P j) = P j
        rw [if_neg hlt]
      rw [hleft1, hright, hleft2]

/-- If nobody demotes the current winner, the winner stays the winner. -/
lemma monotonicity
    (g : SCF ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (hnm : NonManipulable g X)
    {P P' : SProfile ι σ}
    (hmono :
      ∀ i : ι, ∀ a : σ,
        (P i).lt a (g P) →
        (P' i).lt a (g P)) :
    g P' = g P := by
  classical
  have hnm' := (nonManipulable_iff (g := g) (X := X)).mp hnm
  let Q : ℕ → SProfile ι σ := fun k => switchProfile P P' k
  have hQ0 : Q 0 = P := by
    funext i
    simp [Q, switchProfile]
  have hQall : Q (Fintype.card ι) = P' := by
    funext i
    have hi : (Fintype.equivFin ι i : ℕ) < Fintype.card ι := by
      exact (Fintype.equivFin ι i).is_lt
    simp [Q, switchProfile, hi]
  have hconst :
      ∀ k, k ≤ Fintype.card ι → g (Q k) = g P := by
    intro k hk
    induction' k with k ih
    · simp [Q, hQ0]
    · have hk' : k < Fintype.card ι := Nat.lt_of_succ_le hk
      rcases switchProfile_succ (P := P) (P' := P') k hk' with ⟨i, hi⟩
      have hi' : Q (k + 1) = sProfileUpdate (Q k) i (P' i) := by
        simpa [Q] using hi
      rw [hi']
      by_cases hEq : g (Q k) = g (sProfileUpdate (Q k) i (P' i))
      · rw [hEq.symm, ih (Nat.le_of_lt hk')]
      · have hkEq : g (Q k) = g P := ih (Nat.le_of_lt hk')
        have hmem1 : g (Q k) ∈ X := hchoose (Q k)
        have hmem2 : g (sProfileUpdate (Q k) i (P' i)) ∈ X := by
          exact hchoose (sProfileUpdate (Q k) i (P' i))
        have hstrict := hnm' (Q k) i (P' i) hmem1 hmem2 hEq
        have hstrict1 :
            (Q k i).lt (g (sProfileUpdate (Q k) i (P' i))) (g P) := by
          rw [← hkEq]
          exact hstrict.1
        have hstrict2 :
            (P' i).lt (g P) (g (sProfileUpdate (Q k) i (P' i))) := by
          rw [← hkEq]
          exact hstrict.2
        have hPi_or_P'i : Q k i = P i ∨ Q k i = P' i := by
          by_cases hklt : (Fintype.equivFin ι i : ℕ) < k
          · right
            simp [Q, switchProfile, hklt]
          · left
            simp [Q, switchProfile, hklt]
        rcases hPi_or_P'i with hOld | hNew
        · have hPi :
              (P i).lt (g (sProfileUpdate (Q k) i (P' i))) (g P) := by
            simpa [hOld] using hstrict1
          have hPi' :
              (P' i).lt (g (sProfileUpdate (Q k) i (P' i))) (g P) := by
            exact hmono i (g (sProfileUpdate (Q k) i (P' i))) hPi
          exfalso
          exact (P' i).irrefl _ ((P' i).trans hstrict2 hPi')
        · have hP'i :
              (P' i).lt (g (sProfileUpdate (Q k) i (P' i))) (g P) := by
            simpa [hNew] using hstrict1
          exfalso
          exact (P' i).irrefl _ ((P' i).trans hstrict2 hP'i)
  rw [← hQall]
  exact hconst (Fintype.card ι) le_rfl

end NonManipAndMonotonicity

section PairTopHelpers

variable {ι σ : Type*}
variable [Fintype ι] [DecidableEq ι] [DecidableEq σ]

lemma topProfile_pair_eq_swap
    (P : SProfile ι σ) (a b : σ) :
    topProfile ({a, b} : Finset σ) P = topProfile ({b, a} : Finset σ) P := by
  funext i
  have hswap : ({a, b} : Finset σ) = ({b, a} : Finset σ) := by
    ext x
    simp [or_comm]
  simp [topProfile, hswap]

end PairTopHelpers

section TopUnanimityAndStrictRoute

variable {ι σ : Type*}
variable [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Nonempty ι]

lemma top_unanimity
    (g : SCF ι σ) (X S : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X)
    (hS : S.Nonempty)
    (hSX : S ⊆ X)
    (P : SProfile ι σ) :
    g (topProfile S P) ∈ S := by
  classical
  rcases hS with ⟨a, haS⟩
  have haX : a ∈ X := hSX haS
  rcases honto a haX with ⟨P₀, hP₀⟩
  let Q₀ : SProfile ι σ := topProfile S P₀
  let T : SProfile ι σ := topProfile S P
  have hQ₀a : g Q₀ = a := by
    have hmono₀ :
        ∀ i : ι, ∀ x : σ,
          (P₀ i).lt x (g P₀) →
          (Q₀ i).lt x (g P₀) := by
      intro i x hx
      rw [hP₀] at hx ⊢
      by_cases hxS : x ∈ S
      · have hiff :
            (Q₀ i).lt x a ↔ (P₀ i).lt x a := by
          simp [Q₀, topProfile, topifyLin_mem_mem hxS haS]
        exact hiff.2 hx
      · have : (Q₀ i).lt x a := by
          simp [Q₀, topProfile, topifyLin_not_mem_mem hxS haS]
        exact this
    have hQQ : g Q₀ = g P₀ := by
      exact monotonicity g X hchoose hnm hmono₀
    rw [hP₀] at hQQ
    exact hQQ
  let R : ℕ → SProfile ι σ := fun k => switchProfile Q₀ T k
  have hR0 : R 0 = Q₀ := by
    funext i
    simp [R, switchProfile]
  have hRall : R (Fintype.card ι) = T := by
    funext i
    have hi : (Fintype.equivFin ι i : ℕ) < Fintype.card ι := by
      exact (Fintype.equivFin ι i).is_lt
    simp [R, switchProfile, hi]
  have hmem :
      ∀ k, k ≤ Fintype.card ι → g (R k) ∈ S := by
    intro k hk
    induction' k with k ih
    · simpa [hR0, hQ₀a] using haS
    · have hk' : k < Fintype.card ι := Nat.lt_of_succ_le hk
      rcases switchProfile_succ (P := Q₀) (P' := T) k hk' with ⟨i, hi⟩
      have hi' : R (k + 1) = sProfileUpdate (R k) i (T i) := by
        simpa [R] using hi
      rw [hi']
      by_cases hEq : g (R k) = g (sProfileUpdate (R k) i (T i))
      · rw [hEq.symm]
        exact ih (Nat.le_of_lt hk')
      · have holdS : g (R k) ∈ S := ih (Nat.le_of_lt hk')
        by_cases hnewS : g (sProfileUpdate (R k) i (T i)) ∈ S
        · exact hnewS
        · have hmem1 : g (R k) ∈ X := hchoose (R k)
          have hmem2 : g (sProfileUpdate (R k) i (T i)) ∈ X := by
            exact hchoose (sProfileUpdate (R k) i (T i))
          have hstrict :=
            ((nonManipulable_iff (g := g) (X := X)).mp hnm)
              (R k) i (T i) hmem1 hmem2 hEq
          have htop :
              (T i).lt (g (sProfileUpdate (R k) i (T i))) (g (R k)) := by
            simpa [T, topProfile] using
              (topifyLin_not_mem_mem
                (S := S) (L := P i)
                (x := g (sProfileUpdate (R k) i (T i)))
                (y := g (R k))
                hnewS holdS)
          exfalso
          exact (T i).irrefl _ ((T i).trans hstrict.2 htop)
  have hfinal : g (R (Fintype.card ι)) ∈ S := hmem (Fintype.card ι) le_rfl
  simpa [T, hRall] using hfinal

lemma swf_binary_choice_mem_pair
    (g : SCF ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X)
    (P : SProfile ι σ) (a b : σ)
    (ha : a ∈ X) (hb : b ∈ X) :
    g (topProfile ({a, b} : Finset σ) P) ∈ ({a, b} : Finset σ) := by
  apply top_unanimity g X ({a, b} : Finset σ) hchoose honto hnm
  · simp
  · intro x hx
    simp [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
 

lemma binary_top_choice_eq_left
    (g : SCF ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X)
    (P : SProfile ι σ) (a b : σ)
    (ha : a ∈ X) (hb : b ∈ X)
    (hall : ∀ i : ι, (P i).lt b a) :
    g (topProfile ({a, b} : Finset σ) P) = a := by
  classical
  let Pa : SProfile ι σ := topProfile ({a} : Finset σ) P
  let Pab : SProfile ι σ := topProfile ({a, b} : Finset σ) P
  have hPa_mem : g Pa ∈ ({a} : Finset σ) := by
    apply top_unanimity g X ({a} : Finset σ) hchoose honto hnm
    · simp
    · intro x hx
      simp at hx
      subst x
      exact ha

  have hPa_eq : g Pa = a := by
    simpa [Pa] using hPa_mem
  have hmono :
      ∀ i : ι, ∀ x : σ,
        (Pa i).lt x (g Pa) →
        (Pab i).lt x (g Pa) := by
    intro i x hx
    rw [hPa_eq] at hx ⊢
    by_cases hxa : x = a
    · subst x
      exact False.elim ((Pa i).irrefl _ hx)
    · by_cases hxb : x = b
      · subst x
        have hiff :
            (Pab i).lt b a ↔ (P i).lt b a := by
          simpa [Pa, Pab, topProfile] using
            (topifyLin_mem_mem
              (S := ({a, b} : Finset σ)) (L := P i)
              (x := b) (y := a)
              (by simp) (by simp))
        exact hiff.2 (hall i)
      · have hx_not_ab : x ∉ ({a, b} : Finset σ) := by
          simp [hxa, hxb]
        have : (Pab i).lt x a := by
          simpa [Pab, topProfile] using
            (topifyLin_not_mem_mem
              (S := ({a, b} : Finset σ)) (L := P i)
              (x := x) (y := a)
              hx_not_ab (by simp))
        exact this
  have hEq : g Pab = g Pa := by
    exact monotonicity g X hchoose hnm hmono
  rw [hPa_eq] at hEq
  simpa [Pab] using hEq

/-- Nipkow-style induced strict social relation. -/
def swfStrict
    (g : SCF ι σ)
    (P : SProfile ι σ) : σ → σ → Prop :=
  fun a b => a ≠ b ∧ g (topProfile ({a, b} : Finset σ) P) = b

def SWeakParetoStrict (f : SProfile ι σ → σ → σ → Prop) (X : Finset σ) : Prop :=
  ∀ a b, a ∈ X → b ∈ X → ∀ P : SProfile ι σ,
    (∀ i : ι, (P i).lt a b) → f P a b

def SIIAStrict (f : SProfile ι σ → σ → σ → Prop) (X : Finset σ) : Prop :=
  ∀ P P' : SProfile ι σ, ∀ a b,
    a ∈ X → b ∈ X →
    (∀ i : ι, SameOrder ((P i).toPrefOrder).rel ((P' i).toPrefOrder).rel a b a b) →
    (f P a b ↔ f P' a b)

def SIsDictatorshipStrict (f : SProfile ι σ → σ → σ → Prop) (X : Finset σ) : Prop :=
  ∃ i : ι, ∀ P : SProfile ι σ, ∀ a b : σ,
    a ∈ X → b ∈ X →
    (f P a b ↔ (P i).lt a b)

lemma topProfile_pair_strict_iff'
    (P : SProfile ι σ) (a b : σ) (i : ι)
    (hab : a ≠ b) :
    (topProfile ({a, b} : Finset σ) P i).lt a b ↔ (P i).lt a b := by
  simpa [topProfile] using
    (topifyLin_mem_mem
      (S := ({a, b} : Finset σ)) (L := P i)
      (x := a) (y := b)
      (by simp [hab]) (by simp))

lemma topProfile_pair_sameOrder'
    (P P' : SProfile ι σ) (a b : σ)
    (hab : a ≠ b)
    (hsame : ∀ i : ι, SameOrder ((P i).toPrefOrder).rel ((P' i).toPrefOrder).rel a b a b) :
    ∀ i : ι,
      (topProfile ({a, b} : Finset σ) P i).lt a b ↔
      (topProfile ({a, b} : Finset σ) P' i).lt a b := by
  intro i
  have h1 : (P i).lt a b ↔ (P' i).lt a b := by
    have hs := hsame i
    constructor
    · intro h
      have hstrict : StrictPref ((P i).toPrefOrder) a b := by
        exact (LinBallot.toPrefOrder_strict_iff (P i) (x := a) (y := b)).2 h
      have hstrict' : StrictPref ((P' i).toPrefOrder) a b := by
        exact hs.2.1.mp hstrict
      exact (LinBallot.toPrefOrder_strict_iff (P' i) (x := a) (y := b)).1 hstrict'
    · intro h
      have hstrict : StrictPref ((P' i).toPrefOrder) a b := by
        exact (LinBallot.toPrefOrder_strict_iff (P' i) (x := a) (y := b)).2 h
      have hstrict' : StrictPref ((P i).toPrefOrder) a b := by
        exact hs.2.1.mpr hstrict
      exact (LinBallot.toPrefOrder_strict_iff (P i) (x := a) (y := b)).1 hstrict'
  constructor
  · intro h
    exact ((topProfile_pair_strict_iff' P a b i hab).1 h |> h1.mp
      |> (topProfile_pair_strict_iff' P' a b i hab).2)
  · intro h
    exact ((topProfile_pair_strict_iff' P' a b i hab).1 h |> h1.mpr
      |> (topProfile_pair_strict_iff' P a b i hab).2)

lemma swfStrict_weakPareto
    (g : SCF ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X) :
    SWeakParetoStrict (swfStrict g) X := by
  classical
  intro a b ha hb P hall
  have i0 : ι := Classical.choice ‹Nonempty ι›
  have hab : a ≠ b := by
    intro hEq
    subst hEq
    exact (P i0).irrefl _ (hall i0)
  refine ⟨hab, ?_⟩
  have hchoice_ba : g (topProfile ({b, a} : Finset σ) P) = b := by
    exact binary_top_choice_eq_left g X hchoose honto hnm P b a hb ha hall
  have hswap : topProfile ({b, a} : Finset σ) P = topProfile ({a, b} : Finset σ) P := by
    exact topProfile_pair_eq_swap P b a
  simpa [hswap] using hchoice_ba

lemma swfStrict_iia
    (g : SCF ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X) :
    SIIAStrict (swfStrict g) X := by
  classical
  intro P P' a b ha hb hsame
  by_cases hab : a = b
  · subst hab
    constructor
    · intro h
      exact False.elim (h.1 rfl)
    · intro h
      exact False.elim (h.1 rfl)
  · let S : Finset σ := ({a, b} : Finset σ)
    constructor
    · intro habP
      rcases habP with ⟨hab_ne, hchoiceP⟩
      refine ⟨hab_ne, ?_⟩
      have hpair :
          ∀ i : ι,
            (topProfile S P i).lt a b ↔
            (topProfile S P' i).lt a b := by
        intro i
        simpa [S] using topProfile_pair_sameOrder' P P' a b hab hsame i
      have hmono :
          ∀ i : ι, ∀ x : σ,
            (topProfile S P i).lt x (g (topProfile S P)) →
            (topProfile S P' i).lt x (g (topProfile S P)) := by
        intro i x hx
        rw [hchoiceP] at hx ⊢
        by_cases hxb : x = b
        · subst hxb
          exact False.elim ((topProfile S P i).irrefl _ hx)
        · by_cases hxa : x = a
          · subst hxa
            exact (hpair i).mp hx
          · have hx_not_S : x ∉ S := by
              simp [S, hxa, hxb]
            have : (topProfile S P' i).lt x b := by
              have hb_in_S : b ∈ S := by
                simp [S]
              simpa [S, topProfile] using
                (topifyLin_not_mem_mem
                  (S := S) (L := P' i)
                  (x := x) (y := b)
                  hx_not_S hb_in_S)
            exact this
      have hEq : g (topProfile S P') = g (topProfile S P) := by
        exact monotonicity g X hchoose hnm
          (P := topProfile S P)
          (P' := topProfile S P') hmono
      rw [hchoiceP] at hEq
      simpa [S] using hEq
    · intro habP'
      rcases habP' with ⟨hab_ne, hchoiceP'⟩
      refine ⟨hab_ne, ?_⟩
      have hpair :
          ∀ i : ι,
            (topProfile S P' i).lt a b ↔
            (topProfile S P i).lt a b := by
        intro i
        have htmp :
            (topProfile S P i).lt a b ↔
            (topProfile S P' i).lt a b := by
          simpa [S] using topProfile_pair_sameOrder' P P' a b hab hsame i
        exact htmp.symm
      have hmono :
          ∀ i : ι, ∀ x : σ,
            (topProfile S P' i).lt x (g (topProfile S P')) →
            (topProfile S P i).lt x (g (topProfile S P')) := by
        intro i x hx
        rw [hchoiceP'] at hx ⊢
        by_cases hxb : x = b
        · subst hxb
          exact False.elim ((topProfile S P' i).irrefl _ hx)
        · by_cases hxa : x = a
          · subst hxa
            exact (hpair i).mp hx
          · have hx_not_S : x ∉ S := by
              simp [S, hxa, hxb]
            have : (topProfile S P i).lt x b := by
              have hb_in_S : b ∈ S := by
                simp [S]
              simpa [S, topProfile] using
                (topifyLin_not_mem_mem
                  (S := S) (L := P i)
                  (x := x) (y := b)
                  hx_not_S hb_in_S)
            exact this
      have hEq : g (topProfile S P) = g (topProfile S P') := by
        exact monotonicity g X hchoose hnm
          (P := topProfile S P')
          (P' := topProfile S P) hmono
      rw [hchoiceP'] at hEq
      simpa [S] using hEq

lemma swfStrict_dictator_implies_choice_dictator
    (g : SCF ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X)
    (hdict : SIsDictatorshipStrict (swfStrict g) X) :
    IsChoiceDictatorship g X := by
  classical
  rcases hdict with ⟨i, hdict_i⟩
  refine ⟨i, ?_⟩
  intro P y hyX hyNe
  set q : σ := y with hq
  let w : σ := g P
  let S : Finset σ := insert w ({q} : Finset σ)
  let T : Finset σ := insert q ({w} : Finset σ)
  have hqX : q ∈ X := by
    simpa [hq] using hyX
  have hqNe : q ≠ g P := by
    simpa [hq] using hyNe
  have hwX : w ∈ X := hchoose P
  have hwq_ne : w ≠ q := by
    intro h
    apply hqNe
    simpa [w] using h.symm
  have hS_w : w ∈ S := by
    simp [S]
  have hS_q : q ∈ S := by
    simp [S]
  have hT_eq_S : T = S := by
    ext u
    simp [S, T, or_comm]
  have htopchoice : g (topProfile S P) = w := by
    have hmono :
        ∀ j : ι, ∀ t : σ,
          (P j).lt t w →
          (topProfile S P j).lt t w := by
      intro j t ht
      by_cases htw : t = w
      · subst htw
        exact False.elim ((P j).irrefl _ ht)
      · by_cases htq : t = q
        · subst htq
          have hiff :
              (topProfile S P j).lt q w ↔ (P j).lt q w := by
            simpa [S, topProfile] using
              (topifyLin_mem_mem
                (S := S) (L := P j)
                (x := q) (y := w)
                hS_q hS_w)
          exact hiff.2 ht
        · have ht_not_S : t ∉ S := by
            simp [S, htw, htq]
          have : (topProfile S P j).lt t w := by
            simpa [S, topProfile] using
              (topifyLin_not_mem_mem
                (S := S) (L := P j)
                (x := t) (y := w)
                ht_not_S hS_w)
          exact this
    exact monotonicity g X hchoose hnm
      (P := P) (P' := topProfile S P) hmono
  have hqw_choice : g (topProfile T P) = w := by
    simpa [hT_eq_S] using htopchoice
  have hqw : swfStrict g P q w := by
    refine ⟨hwq_ne.symm, ?_⟩
    simpa [swfStrict, T] using hqw_choice
  have hdict_qw : (swfStrict g P q w ↔ (P i).lt q w) := by
    exact hdict_i P q w hqX hwX
  exact hdict_qw.mp hqw

theorem gibbard_satterthwaite
    (g : SCF ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X)
    (hX : 3 ≤ X.card)
    (harrow :
      SWeakParetoStrict (swfStrict g) X →
      SIIAStrict (swfStrict g) X →
      SIsDictatorshipStrict (swfStrict g) X) :
    IsChoiceDictatorship g X := by
  have hwp : SWeakParetoStrict (swfStrict g) X :=
    swfStrict_weakPareto g X hchoose honto hnm
  have hiia : SIIAStrict (swfStrict g) X :=
    swfStrict_iia g X hchoose honto hnm
  have hdict : SIsDictatorshipStrict (swfStrict g) X :=
    harrow hwp hiia
  exact swfStrict_dictator_implies_choice_dictator g X hchoose honto hnm hdict

end TopUnanimityAndStrictRoute

end SocialChoiceTheory
