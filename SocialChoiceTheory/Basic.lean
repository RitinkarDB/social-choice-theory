import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic

open Relation

namespace EcoLean
namespace SocialChoice

section FinsetLemmas

variable {α : Type*} [DecidableEq α]
variable {s : Finset α} {a b : α}

namespace Finset

lemma existsDistinctMemOfNeSingleton
    (hs₁ : s.Nonempty) (hs₂ : s ≠ {a}) :
    ∃ b ∈ s, b ≠ a := by
  classical
  by_contra h
  push_neg at h
  apply hs₂
  ext x
  constructor
  · intro hx
    have hx' := h x hx
    simpa [hx']
  · intro hx
    rcases hs₁ with ⟨y, hy⟩
    have hy' : y = a := h y hy
    have hx' : x = a := by simpa using hx
    subst hy'
    subst hx'
    simpa using hy

lemma existsSecondDistinctMem
    (hs : 2 ≤ s.card) (ha : a ∈ s) :
    ∃ b ∈ s, b ≠ a := by
  classical
  have hcard : 1 ≤ (s.erase a).card := by
    have hs' : 2 ≤ (s.erase a).card + 1 := by
      simpa [Finset.card_erase_add_one ha] using hs
    omega
  have hpos : 0 < (s.erase a).card := by omega
  have hne : (s.erase a).Nonempty := Finset.card_pos.1 hpos
  rcases hne with ⟨b, hb⟩
  exact ⟨b, (Finset.mem_erase.1 hb).2, (Finset.mem_erase.1 hb).1⟩

lemma existsThirdDistinctMem
    (hs : 2 < s.card) (ha : a ∈ s) (hb : b ∈ s) (h : a ≠ b) :
    ∃ c ∈ s, c ≠ a ∧ c ≠ b := by
  classical
  have hba : a ∈ s.erase b := Finset.mem_erase.mpr ⟨h, ha⟩
  have h1 : ((s.erase b).erase a).card + 1 = (s.erase b).card := by
    simpa using Finset.card_erase_add_one hba
  have h2 : (s.erase b).card + 1 = s.card := by
    simpa using Finset.card_erase_add_one hb
  have hpos : 0 < ((s.erase b).erase a).card := by
    omega
  have hne : ((s.erase b).erase a).Nonempty := Finset.card_pos.mp hpos
  rcases hne with ⟨c, hc⟩
  have hce : c ∈ s.erase b := (Finset.mem_erase.mp hc).2
  have hca : c ≠ a := (Finset.mem_erase.mp hc).1
  have hcb : c ≠ b := (Finset.mem_erase.mp hce).1
  have hcs : c ∈ s := (Finset.mem_erase.mp hce).2
  exact ⟨c, hcs, hca, hcb⟩

lemma nonemptyOfMem (ha : a ∈ s) : s.Nonempty := ⟨a, ha⟩

end Finset

namespace Relation

lemma forallExistsTransGen
    (R : α → α → Prop)
    (hR : ∀ a ∈ s, ∃ b ∈ s, R b a) :
    ∀ a ∈ s, ∃ b ∈ s, TransGen R b a := by
  intro a ha
  rcases hR a ha with ⟨b, hb, hab⟩
  exact ⟨b, hb, TransGen.single hab⟩

end Relation

end FinsetLemmas

open Finset

section BasicDefs

variable {σ ι : Type*}
variable {x y z a b : σ}
variable {R R' : σ → σ → Prop}

/-- Strict preference induced by a weak relation. -/
def StrictPref (R : σ → σ → Prop) (x y : σ) : Prop :=
  R x y ∧ ¬ R y x

/-- Indifference induced by a weak relation. -/
def Indiff (R : σ → σ → Prop) (x y : σ) : Prop :=
  R x y ∧ R y x

lemma strictPref_iff_of_iff
    (h₁ : R a b ↔ R' a b)
    (h₂ : R b a ↔ R' b a) :
    (StrictPref R a b ↔ StrictPref R' a b) ∧
    (StrictPref R b a ↔ StrictPref R' b a) := by
  constructor <;> simp [StrictPref, h₁, h₂]

lemma indiff_trans
    (htrans : Transitive R)
    (h1 : Indiff R x y) (h2 : Indiff R y z) :
    Indiff R x z := by
  exact ⟨htrans h1.1 h2.1, htrans h2.2 h1.2⟩

lemma strictPref_trans_indiff
    (htrans : Transitive R)
    (h1 : StrictPref R x y) (h2 : Indiff R y z) :
    StrictPref R x z := by
  refine ⟨htrans h1.1 h2.1, ?_⟩
  intro hzx
  exact h1.2 (htrans h2.1 hzx)

lemma indiff_trans_strictPref
    (htrans : Transitive R)
    (h1 : Indiff R x y) (h2 : StrictPref R y z) :
    StrictPref R x z := by
  refine ⟨htrans h1.1 h2.1, ?_⟩
  intro hzx
  exact h2.2 (htrans hzx h1.1)

lemma strictPref_trans
    (htrans : Transitive R)
    (h1 : StrictPref R x y) (h2 : StrictPref R y z) :
    StrictPref R x z := by
  refine ⟨htrans h1.1 h2.1, ?_⟩
  intro hzx
  exact h2.2 (htrans hzx h1.1)

lemma rel_of_not_strictPref_total
    (htot : Total R) (h : ¬ StrictPref R y x) :
    R x y := by
  rcases htot x y with hxy | hyx
  · exact hxy
  · by_contra hxy
    exact h ⟨hyx, hxy⟩

lemma not_strictPref_of_reverse
    (h : StrictPref R x y) :
    ¬ StrictPref R y x := by
  intro hyx
  exact hyx.2 h.1

lemma not_strictPref_of_not_rel
    (h : ¬ R x y) :
    ¬ StrictPref R x y := by
  intro hxy
  exact h hxy.1

lemma false_of_strictPref_self
    (h : StrictPref R x x) :
    False := by
  exact h.2 h.1

/-- Same order of a pair across two relations. -/
def SameOrder
    (R R' : σ → σ → Prop) (x y x' y' : σ) : Prop :=
  ((R x y ↔ R' x' y') ∧ (R y x ↔ R' y' x')) ∧
  (StrictPref R x y ↔ StrictPref R' x' y') ∧
  (StrictPref R y x ↔ StrictPref R' y' x')

/-- Slimmer pairwise version using only strict preference. -/
def SameOrder'
    (R R' : σ → σ → Prop) (x y x' y' : σ) : Prop :=
  (StrictPref R x y ↔ StrictPref R' x' y') ∧
  (StrictPref R y x ↔ StrictPref R' y' x')

lemma sameOrder_of_strict_strict
    (hR : StrictPref R x y) (hR' : StrictPref R' x y) :
    SameOrder R R' x y x y := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact Iff.intro (fun _ => hR'.1) (fun _ => hR.1)
    · exact Iff.intro
        (fun hyx => False.elim (hR.2 hyx))
        (fun hyx => False.elim (hR'.2 hyx))
  · exact Iff.intro (fun _ => hR') (fun _ => hR)
  · exact Iff.intro
      (fun hyx => False.elim ((not_strictPref_of_reverse hR) hyx))
      (fun hyx => False.elim ((not_strictPref_of_reverse hR') hyx))

lemma sameOrder_of_reverse_strict
    (hR : StrictPref R y x) (hR' : StrictPref R' y x) :
    SameOrder R R' x y x y := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact Iff.intro
        (fun hxy => False.elim (hR.2 hxy))
        (fun hxy => False.elim (hR'.2 hxy))
    · exact Iff.intro (fun _ => hR'.1) (fun _ => hR.1)
  · exact Iff.intro
      (fun hxy => False.elim ((not_strictPref_of_reverse hR) hxy))
      (fun hxy => False.elim ((not_strictPref_of_reverse hR') hxy))
  · exact Iff.intro (fun _ => hR') (fun _ => hR)

lemma sameOrder'_comm :
    SameOrder' R R' x y x y ↔ SameOrder' R R' y x y x := by
  exact and_comm

def IsMaximalElement
    (x : σ) (S : Finset σ) (R : σ → σ → Prop) : Prop :=
  ∀ y ∈ S, ¬ StrictPref R y x

def IsBestElement
    (x : σ) (S : Finset σ) (R : σ → σ → Prop) : Prop :=
  ∀ y ∈ S, R x y

noncomputable def maximalSet [DecidableEq σ]
    (S : Finset σ) (R : σ → σ → Prop) : Finset σ := by
  classical
  exact S.filter (fun x => IsMaximalElement x S R)

noncomputable def choiceSet [DecidableEq σ]
    (S : Finset σ) (R : σ → σ → Prop) : Finset σ := by
  classical
  exact S.filter (fun x => IsBestElement x S R)

lemma maximalElement_of_mem_maximalSet
    [DecidableEq σ] {r : σ → σ → Prop} {s : Finset σ} {x : σ}
    (h : x ∈ maximalSet s r) :
    IsMaximalElement x s r := by
  simp [maximalSet] at h
  exact h.2

lemma mem_maximalSet_of_maximalElement
    [DecidableEq σ] {r : σ → σ → Prop} {s : Finset σ} {x : σ}
    (hx : x ∈ s) (h : IsMaximalElement x s r) :
    x ∈ maximalSet s r := by
  simp [maximalSet, hx, h]

lemma maximalSet_subset
    [DecidableEq σ] (s : Finset σ) (r : σ → σ → Prop) :
    maximalSet s r ⊆ s := by
  classical
  intro x hx
  exact (Finset.mem_filter.mp hx).1

lemma isMaximal_of_singleton
    [DecidableEq σ] {R : σ → σ → Prop}
    (hR : Reflexive R) (x : σ) :
    IsMaximalElement x ({x} : Finset σ) R := by
  intro y hy
  have hy' : y = x := by
    simpa using hy
  subst hy'
  intro h
  exact h.2 (hR _)


lemma maximalSet_eq_empty_of_empty
    [DecidableEq σ] (R : σ → σ → Prop) :
    maximalSet (∅ : Finset σ) R = ∅ := by
  simp [maximalSet]

lemma choiceSet_eq_empty_of_empty
    [DecidableEq σ] (R : σ → σ → Prop) :
    choiceSet (∅ : Finset σ) R = ∅ := by
  simp [choiceSet]

lemma choiceSet_subset_maximalSet
    [DecidableEq σ] (S : Finset σ) (R : σ → σ → Prop) :
    choiceSet S R ⊆ maximalSet S R := by
  classical
  intro a ha
  rcases Finset.mem_filter.mp ha with ⟨haS, haBest⟩
  apply Finset.mem_filter.mpr
  refine ⟨haS, ?_⟩
  intro y hy
  intro hya
  exact hya.2 (haBest y hy)

end BasicDefs

section QuasiOrders

variable {σ : Type*}

/-- Quasi-ordering as a bundled object. -/
structure QuasiOrder (α : Type*) where
  rel : α → α → Prop
  refl : Reflexive rel
  trans : Transitive rel

instance : CoeFun (QuasiOrder σ) (fun _ => σ → σ → Prop) where
  coe r := r.rel

namespace QuasiOrder

lemma eq_coe (r : QuasiOrder σ) : r.rel = r := rfl

end QuasiOrder

open Finset

lemma maximal_of_finite_quasiOrdered
    [DecidableEq σ]
    (r : QuasiOrder σ)
    (S : Finset σ) (hS : S.Nonempty) :
    ∃ x ∈ S, IsMaximalElement x S r := by
  classical
  refine Finset.induction_on S ?h0 ?hstep hS
  · intro h
    cases h with
    | intro x hx => cases hx
  · intro a s ha_not_mem ih hs_nonempty
    by_cases hs : s.Nonempty
    · rcases ih hs with ⟨x, hxS, hxmax⟩
      by_cases hax : StrictPref r a x
      · refine ⟨a, by simp, ?_⟩
        intro b hb
        by_cases hba : b = a
        · subst hba
          intro haa
          exact haa.2 (r.refl _)
        · have hbS : b ∈ s := by
            simpa [hba] using hb
          intro hba_strict
          exact hxmax b hbS (strictPref_trans r.trans hba_strict hax)
      · refine ⟨x, by simp [hxS], ?_⟩
        intro b hb
        by_cases hba : b = a
        · subst hba
          simpa using hax
        · exact hxmax b (by simpa [hba] using hb)
    · have hs' : s = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hs
      subst hs'
      refine ⟨a, by simp, ?_⟩
      simpa using isMaximal_of_singleton r.refl a

lemma choiceSet_of_singleton
    [DecidableEq σ]
    {r : σ → σ → Prop} (hr : Reflexive r) (x : σ) :
    choiceSet ({x} : Finset σ) r = {x} := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hyx, _⟩
    simpa using hyx
  · intro hy
    apply Finset.mem_filter.mpr
    refine ⟨by simpa [hy] using Finset.mem_singleton_self x, ?_⟩
    intro z hz
    have hz' : z = x := by
      simpa using hz
    have hy' : y = x := by
      simpa using hy
    rw [hy', hz']
    exact hr x

lemma singleton_choiceSet
    [DecidableEq σ]
    {r : σ → σ → Prop}
    (x y : σ) (hxy : x ≠ y) (hR : Reflexive r) :
    StrictPref r x y ↔ ({x} : Finset σ) = choiceSet ({x, y} : Finset σ) r := by
  classical
  constructor
  · intro h
    ext z
    constructor
    · intro hz
      have hz' : z = x := by
        simpa using hz
      apply Finset.mem_filter.mpr
      refine ⟨by simpa [hz'], ?_⟩
      intro w hw
      have hw' : w = x ∨ w = y := by
        simpa using hw
      rcases hw' with hwx | hwy
      · rw [hz', hwx]
        exact hR x
      · rw [hz', hwy]
        exact h.1
    · intro hz
      rcases Finset.mem_filter.mp hz with ⟨hzS, hzBest⟩
      by_cases hzx : z = x
      · simpa [hzx]
      · have hzy : z = y := by
          have : z = x ∨ z = y := by
            simpa using hzS
          rcases this with h1 | h2
          · exact False.elim (hzx h1)
          · exact h2
        have hyx : r y x := by
          rw [← hzy]
          exact hzBest x (by simp)
        exfalso
        exact h.2 hyx
  · intro hEq
    have hx : x ∈ choiceSet ({x, y} : Finset σ) r := by
      rw [← hEq]
      simp
    rcases Finset.mem_filter.mp hx with ⟨hxS, hxBest⟩
    have hxy' : r x y := by
      exact hxBest y (by simp)
    have hy_not : y ∉ choiceSet ({x, y} : Finset σ) r := by
      intro hy_mem
      rw [← hEq] at hy_mem
      have : y = x := by
        simpa using hy_mem
      exact hxy this.symm
    have hyx_not : ¬ r y x := by
      intro hyx
      apply hy_not
      apply Finset.mem_filter.mpr
      refine ⟨by simp, ?_⟩
      intro z hz
      have hz' : z = x ∨ z = y := by
        simpa using hz
      rcases hz' with hzx | hzy
      · rw [hzx]
        exact hyx
      · rw [hzy]
        exact hR y
    exact ⟨hxy', hyx_not⟩

lemma choiceEq_maximal_of_quasi
    [DecidableEq σ]
    {r : QuasiOrder σ}
    (S : Finset σ) (hS : (choiceSet S r).Nonempty) :
    choiceSet S r = maximalSet S r := by
  classical
  apply Finset.Subset.antisymm
  · exact choiceSet_subset_maximalSet S r
  · intro z hz
    rcases hS with ⟨x, hx⟩
    rcases Finset.mem_filter.mp hz with ⟨hzS, hzmax⟩
    rcases Finset.mem_filter.mp hx with ⟨hxS, hxbest⟩
    apply Finset.mem_filter.mpr
    refine ⟨hzS, ?_⟩
    intro y hy
    have hzx : r z x := by
      by_contra hzx
      exact hzmax x hxS ⟨hxbest z hzS, hzx⟩
    exact r.trans hzx (hxbest y hy)

lemma maximal_indiff_iff_choiceEq_maximal
    [DecidableEq σ]
    (r : QuasiOrder σ)
    (S : Finset σ) (hS : S.Nonempty) :
    (∀ x y, x ∈ maximalSet S r → y ∈ maximalSet S r → Indiff r x y) ↔
      choiceSet S r = maximalSet S r := by
  classical
  constructor
  · intro hyp
    by_contra sets_neq
    obtain ⟨x₀, x₀_in, hx₀⟩ := maximal_of_finite_quasiOrdered r S hS
    have choice_empty : choiceSet S r = ∅ := by
      by_contra hne
      have hchoice_nonempty : (choiceSet S r).Nonempty := by
        by_contra hchoice_empty
        exact hne (Finset.not_nonempty_iff_eq_empty.mp hchoice_empty)
      exact sets_neq (choiceEq_maximal_of_quasi S hchoice_nonempty)
    have x₀_not_in : x₀ ∉ choiceSet S r := by
      rw [choice_empty]
      simp
    have hx₀_not_best : ¬ IsBestElement x₀ S r := by
      intro hxbest
      exact x₀_not_in (Finset.mem_filter.mpr ⟨x₀_in, hxbest⟩)
    unfold IsBestElement at hx₀_not_best
    push_neg at hx₀_not_best
    obtain ⟨x₁, x₁_in, hx₁⟩ := hx₀_not_best

    have hx₀M : x₀ ∈ maximalSet S r := by
      exact mem_maximalSet_of_maximalElement x₀_in hx₀

    have x₁_not_in : x₁ ∉ maximalSet S r := by
      intro x₁_in_max
      exact hx₁ (hyp x₀ x₁ hx₀M x₁_in_max).1

    let T : Finset σ := S.filter (fun z => StrictPref r z x₁ ∧ z ∉ maximalSet S r)

    have h_no_max :
        ¬ ∃ x ∈ T, IsMaximalElement x T r := by
      intro hmax
      rcases hmax with ⟨x, x_in, hxmaxT⟩
      have hx_in : x ∈ S ∧ StrictPref r x x₁ ∧ x ∉ maximalSet S r := by
        simpa [T] using x_in
      rcases hx_in with ⟨hxS, hPx₁, hx_not_max⟩

      have hx_not_max' : ¬ IsMaximalElement x S r := by
        intro hxMaxS
        exact hx_not_max (mem_maximalSet_of_maximalElement hxS hxMaxS)

      unfold IsMaximalElement at hx_not_max'
      push_neg at hx_not_max'
      obtain ⟨y, y_in, hy⟩ := hx_not_max'

      have hy_in_T : y ∈ T := by
        apply Finset.mem_filter.mpr
        refine ⟨y_in, ?_⟩
        refine ⟨strictPref_trans r.trans hy hPx₁, ?_⟩
        intro y_max
        apply hx₁
        exact (indiff_trans_strictPref r.trans
          (hyp x₀ y hx₀M y_max)
          (strictPref_trans r.trans hy hPx₁)).1

      have hy_strict : StrictPref r y x := by
        exact hy

      exact hxmaxT y hy_in_T hy_strict

    have hT_nonempty : T.Nonempty := by
      have x₁_not_max' : ¬ IsMaximalElement x₁ S r := by
        intro hx₁max
        exact x₁_not_in (mem_maximalSet_of_maximalElement x₁_in hx₁max)
      unfold IsMaximalElement at x₁_not_max'
      push_neg at x₁_not_max'
      obtain ⟨x₂, x₂_in, hx₂⟩ := x₁_not_max'
      refine ⟨x₂, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨x₂_in, ?_⟩
      refine ⟨hx₂, ?_⟩
      intro x₂_in_max
      apply hx₁
      exact r.trans (hyp x₀ x₂ hx₀M x₂_in_max).1 hx₂.1

    exact h_no_max (maximal_of_finite_quasiOrdered r T hT_nonempty)

  · intro hEq
    rw [← hEq]
    intro x y x_in y_in
    rcases Finset.mem_filter.mp x_in with ⟨hxS, hxbest⟩
    rcases Finset.mem_filter.mp y_in with ⟨hyS, hybest⟩
    exact ⟨hxbest y hyS, hybest x hxS⟩
section PrefOrders

variable {σ : Type*}

/-- Preference ordering as a bundled object. -/
structure PrefOrder (α : Type*) where
  rel : α → α → Prop
  refl : Reflexive rel
  total : Total rel
  trans : Transitive rel

instance : CoeFun (PrefOrder σ) (fun _ => σ → σ → Prop) where
  coe r := r.rel

namespace PrefOrder

lemma eq_coe (r : PrefOrder σ) : r.rel = r := rfl

lemma reverse {r : PrefOrder σ} {a b : σ} (h : ¬ r a b) : r b a :=
  (r.total a b).resolve_left h

end PrefOrder

/-- Compatibility notions from the original library. -/
def IsSubrelation (Q₁ Q₂ : QuasiOrder σ) : Prop :=
  ∀ x y : σ, (Q₁ x y → Q₂ x y) ∧ ((Q₁ x y ∧ ¬ Q₁ y x) → ¬ Q₂ y x)

def IsCompatible (Q : QuasiOrder σ) (R : PrefOrder σ) : Prop :=
  ∀ x y : σ, (Q x y → R x y) ∧ ((Q x y ∧ ¬ Q y x) → ¬ R y x)

end PrefOrders

end QuasiOrders
end SocialChoice
end EcoLean
