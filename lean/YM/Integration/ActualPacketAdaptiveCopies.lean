import YM.Integration.ActualPacketFiniteCopies
import YM.Integration.ActualBetaCutoff

/-!
Finite row-dependent copies with a stable power cap. The fixed finite grid
is only an indexing device: entries beyond the actual row cutoff are absent.
All kept tokens retain their original geometry. This module constructs no
new analytic or prescribed-jet hypothesis.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualPacketAdaptiveCopies
open Lattice Wilson RG Marker Precision
open Push.AbsoluteSums
open Comparison.Density.RenderM LocalComparison ActualRunPacketRetuning
open ActualPacketFiniteCopies ActualBetaCutoff
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type}
    {D : V → ComparisonDensity.Address.Orbit}
    [DecidableEq V] {S : Census V}

def grid (r : ℕ) : ℕ := (r + 2) / 2

def kept (P : MarkedPackets D G n S) (r k : ℕ) : Prop :=
  (index (grid r) k).2.val ≤ retuningOrder r (P.power (index (grid r) k).1)

def adaptive (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ) : MarkedPackets D G n S where
  mode := (copies P (grid r) c).mode
  rank := (copies P (grid r) c).rank
  power := (copies P (grid r) c).power
  packet k := if kept P r k then (copies P (grid r) c).packet k else none
  marked k T h := by
    split at h
    · exact (copies P (grid r) c).marked k T h
    · cases h
  rankCap := P.rankCap
  powerCap := max P.powerCap (r + 2)
  rank_bounded k T h := by
    split at h
    · exact (copies P (grid r) c).rank_bounded k T h
    · cases h
  power_bounded k T h := by
    split at h
    · rename_i hk
      obtain ⟨Q, hQ, _⟩ := Option.map_eq_some_iff.mp h
      have habs : ((P.power (index (grid r) k).1).natAbs : ℤ) ≤
          (P.powerCap : ℤ) := by
        exact_mod_cast P.power_bounded _ Q hQ
      have he : |P.power (index (grid r) k).1| ≤ (P.powerCap : ℤ) := by
        simpa only [Int.natCast_natAbs] using habs
      have hb := shifted_power_bound r P.powerCap
        (P.power (index (grid r) k).1) he (index (grid r) k).2.val hk
      have hn : ((P.power (index (grid r) k).1 +
          (2 * (index (grid r) k).2.val : ℕ)).natAbs : ℤ) ≤
          (max P.powerCap (r + 2) : ℕ) := by
        simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_ofNat] using hb
      exact_mod_cast hn
    · cases h
  nonnegative_grade k T h := by
    split at h
    · exact (copies P (grid r) c).nonnegative_grade k T h
    · cases h

/-- The original layout and literal even shift are retained. The symmetric
cap is stable under another application at the same requested order. -/
theorem adaptive_layout (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ) (k : ℕ) :
    (adaptive P r c).mode k = P.mode (index (grid r) k).1 ∧
    (adaptive P r c).rank k = P.rank (index (grid r) k).1 ∧
    (adaptive P r c).power k =
      P.power (index (grid r) k).1 + (2 * (index (grid r) k).2.val : ℕ) ∧
    (adaptive P r c).rankCap = P.rankCap ∧
    (adaptive P r c).powerCap = max P.powerCap (r + 2) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The fixed grid has genuinely absent entries above the row's order. -/
theorem inactive_absent (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ) (k : ℕ) (hk : ¬ kept P r k) :
    (adaptive P r c).packet k = none := by
  simp only [adaptive, if_neg hk]

private theorem live_copy (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ) (k : ℕ)
    (T : Token G n (fun v => (D v).Mood) ((adaptive P r c).rank k))
    (h : (adaptive P r c).packet k = some T) :
    kept P r k ∧ (copies P (grid r) c).packet k = some T := by
  by_cases hk : kept P r k
  · exact ⟨hk, by simpa only [adaptive, if_pos hk] using h⟩
  · simp only [inactive_absent P r c k hk] at h
    cases h

/-- Copying never decreases an original row's integer coupling power. -/
theorem original_power_le (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ) (k : ℕ) :
    P.power (index (grid r) k).1 ≤ (adaptive P r c).power k := by
  change P.power (index (grid r) k).1 ≤
    P.power (index (grid r) k).1 + (2 * (index (grid r) k).2.val : ℕ)
  exact le_add_of_nonneg_right (by positivity)

/-- An occupied-row lower bound is preserved independently of the new
positive cap. In particular the original clearing order need not grow. -/
theorem lower_bound (P : MarkedPackets D G n S) (r bound : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ)
    (hfloor : ∀ i T, P.packet i = some T → -(bound : ℤ) ≤ P.power i)
    (k : ℕ)
    (T : Token G n (fun v => (D v).Mood) ((adaptive P r c).rank k))
    (h : (adaptive P r c).packet k = some T) :
    -(bound : ℤ) ≤ (adaptive P r c).power k := by
  obtain ⟨Q, hQ, _⟩ := Option.map_eq_some_iff.mp (live_copy P r c k T h).2
  exact (hfloor _ Q hQ).trans (original_power_le P r c k)

/-- Exact term before removing the zero coefficient padding. -/
theorem adaptive_term (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ) (x : TestSpace D)
    (g : ℝ) (U : Config G n) (k : ℕ) :
    (adaptive P r c).term x g U k =
      if kept P r k then (copies P (grid r) c).term x g U k else 0 := by
  by_cases hk : kept P r k
  · simp only [MarkedPackets.term, adaptive, if_pos hk]
    cases (copies P (grid r) c).packet k <;> rfl
  · simp only [MarkedPackets.term, adaptive, if_neg hk]

/-- Zero coefficients on discarded entries make pruning exact, also at
zero coupling. No signed-power addition is used in this equality. -/
theorem adaptive_term_eq (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ)
    (hc : ∀ e j, retuningOrder r e < j.val → c e j = 0)
    (x : TestSpace D) (g : ℝ) (U : Config G n) (k : ℕ) :
    (adaptive P r c).term x g U k = (copies P (grid r) c).term x g U k := by
  rw [adaptive_term]
  by_cases hk : kept P r k
  · rw [if_pos hk]
  · rw [if_neg hk]
    have hz := hc (P.power (index (grid r) k).1) (index (grid r) k).2
      (Nat.lt_of_not_ge hk)
    cases hP : P.packet (index (grid r) k).1 <;>
      simp [MarkedPackets.term, copies, hP, hz, scaleToken, Token.read, Token.touch]

/-- Full unmasked read equality is termwise and needs no added summability
assumption. The actual Paid receipt supplies summability when needed later. -/
theorem adaptive_read_eq [Fintype V] (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ)
    (hc : ∀ e j, retuningOrder r e < j.val → c e j = 0)
    (x : TestSpace D) (g : ℝ) (U : Config G n) :
    (adaptive P r c).read x g U = (copies P (grid r) c).read x g U := by
  apply tsum_congr
  intro k
  exact congrArg (Poly.send ((copies P (grid r) c).mode k))
    (adaptive_term_eq P r c hc x g U k)

private theorem adaptive_charge (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ) (w : V → ℝ)
    (g width : ℝ) (v : V) (k : ℕ) :
    rowCharge (adaptive P r c) w g width v k =
      if kept P r k then rowCharge (copies P (grid r) c) w g width v k else 0 := by
  by_cases hk : kept P r k
  · simp only [rowCharge, adaptive, if_pos hk]
    split_ifs
    · cases (copies P (grid r) c).packet k <;> rfl
    · rfl
  · simp only [rowCharge, adaptive, if_neg hk]
    split_ifs <;> rfl

/-- Pruning copies preserves every Paid field and the original copied bill.
Only nonnegative discarded root charges are removed. -/
theorem adaptive_paid (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ)
    {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : (copies P (grid r) c).Paid B address region w g width budget
      coverOffset coverSlope) :
    (adaptive P r c).Paid B address region w g width budget
      coverOffset coverSlope := by
  refine
    { width_pos := hP.width_pos
      positive := hP.positive
      coefficient := ?_
      paths := ?_
      addresses := ?_
      symmetry := ?_
      reads := ?_
      multilinear := ?_
      roots := ?_
      cover := ?_
      width_reserved := hP.width_reserved }
  · intro k T h
    exact hP.coefficient k T (live_copy P r c k T h).2
  · intro k T h
    exact hP.paths k T (live_copy P r c k T h).2
  · intro k T h
    exact hP.addresses k T (live_copy P r c k T h).2
  · intro k T h
    exact hP.symmetry k T (live_copy P r c k T h).2
  · intro k T h
    exact hP.reads k T (live_copy P r c k T h).2
  · intro k T h
    exact hP.multilinear k T (live_copy P r c k T h).2
  · intro v
    have hroot : SumBudget (rowCharge (copies P (grid r) c) w g width v) budget := by
      convert hP.roots v using 2
      simp only [rowCharge]
      rename_i i
      split_ifs
      · cases (copies P (grid r) c).packet i <;> rfl
      · rfl
    have hbudget : SumBudget (rowCharge (adaptive P r c) w g width v) budget := by
      apply Extra.Iteration.Cost.mono hroot
      · intro k
        rw [adaptive_charge]
        split_ifs
        · exact hroot.1 k
        · exact le_rfl
      · intro k
        rw [adaptive_charge]
        split_ifs
        · exact le_rfl
        · exact hroot.1 k
    convert hbudget using 2
    simp only [rowCharge]
    rename_i i
    split_ifs
    · cases (adaptive P r c).packet i <;> rfl
    · rfl
  · intro k T h
    exact hP.cover k T (live_copy P r c k T h).2

/-- The uniform per-power scalar bound pays the actual adaptive family at
the same coupling, without a factor counting powers or copy indices. -/
theorem adaptive_paid_of_bound (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (grid r + 1) → ℂ) (g : ℝ) (hg : g ≠ 0)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hc : ∀ e : ℤ, |e| ≤ (P.powerCap : ℤ) →
      (∑ j : Fin (grid r + 1), ‖c e j‖ * ‖(g : ℂ) ^ (2 * j.val)‖) ≤ bound)
    {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid B address region w g width budget coverOffset coverSlope) :
    (adaptive P r c).Paid B address region w g width (budget * bound)
      coverOffset coverSlope :=
  adaptive_paid P r c
    (copies_paid_of_bound P (grid r) c g hg bound hbound hc hP)

end YM.Integration.ActualPacketAdaptiveCopies
end
