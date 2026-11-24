import YM.Integration.ActualPacketCorrectedCoefficients
import YM.Integration.NativePaidPacketColors

/-!
The actual finite packet for the corrected beta chart. The fixed physical
ratio is first paid exactly, then cancelled inside every retained token.
The resulting coefficients are literally the Taylor coefficients and the
physical correction on the original tokens. All fields and independent
tests remain unchanged. Raw regrouping across integer powers is restricted
to nonzero coupling; the cleared zero-coupling contact is separate.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualPacketInterpolatedRetuning
open Lattice Wilson RG Marker Precision
open Comparison.Density.RenderM LocalComparison ActualRunPacketRetuning
open ActualPacketFiniteCopies ActualPacketAdaptiveCopies ActualBetaCutoff
open ActualPacketCorrectedCoefficients ActualBetaRemainder
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type}
    {D : V → ComparisonDensity.Address.Orbit}

private theorem scaled_read {q : ℕ} (c : ℂ)
    (T : Token G n (fun v => (D v).Mood) q)
    (x : TestSpace D) (U : Config G n) :
    (scaleToken c T).read x U = c * T.read x U := by
  unfold Token.read Token.touch scaleToken
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

private theorem scale_mul {q : ℕ} (c d : ℂ)
    (T : Token G n (fun v => (D v).Mood) q) :
    scaleToken c (scaleToken d T) = scaleToken (c * d) T := by
  cases T
  simp only [scaleToken, norm_mul, mul_assoc]

private theorem unit_nonzero (delta physical : ℝ)
    (hdom : 0 < 1 - delta * physical ^ 2) :
    unit delta physical ≠ 0 :=
  inv_ne_zero (Real.sqrt_pos.2 hdom).ne'

/-- The fixed physical retune cancels in every coefficient, before any
coupling-power regrouping or field evaluation. -/
theorem coefficient_cancel (r : ℕ) (delta physical : ℝ) (e : ℤ)
    (j : Fin (grid r + 1)) (hdom : 0 < 1 - delta * physical ^ 2) :
    normalizedCoefficient r delta physical e j *
        (unit delta physical : ℂ) ^ e =
      (rowCoefficient r delta physical e j : ℂ) := by
  have hu : (unit delta physical : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (unit_nonzero delta physical hdom)
  unfold normalizedCoefficient
  calc
    _ = (((unit delta physical : ℂ) ^ e)⁻¹ *
        (unit delta physical : ℂ) ^ e) *
          (rowCoefficient r delta physical e j : ℂ) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (zpow_ne_zero _ hu), one_mul]

variable [DecidableEq V] {S : Census V}

def interpolated (P : MarkedPackets D G n S) (r : ℕ)
    (delta physical : ℝ) : MarkedPackets D G n S :=
  adaptive (retune P (unit delta physical)) r
    (normalizedCoefficient r delta physical)

/-- Original modes, ranks and geometry survive, with the stable cap and
the explicit nonnegative even shift in every row's power. -/
theorem interpolated_layout (P : MarkedPackets D G n S) (r : ℕ)
    (delta physical : ℝ) (k : ℕ) :
    (interpolated P r delta physical).mode k = P.mode (index (grid r) k).1 ∧
    (interpolated P r delta physical).rank k = P.rank (index (grid r) k).1 ∧
    (interpolated P r delta physical).power k =
      P.power (index (grid r) k).1 + (2 * (index (grid r) k).2.val : ℕ) ∧
    (interpolated P r delta physical).rankCap = P.rankCap ∧
    (interpolated P r delta physical).powerCap = max P.powerCap (r + 2) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The token itself is the original token with the direct correcting
coefficient. Grid entries above the row cutoff are genuinely absent. -/
theorem interpolated_packet (P : MarkedPackets D G n S) (r : ℕ)
    (delta physical : ℝ) (hdom : 0 < 1 - delta * physical ^ 2) (k : ℕ) :
    (interpolated P r delta physical).packet k =
      if kept P r k then
        (P.packet (index (grid r) k).1).map
          (scaleToken (rowCoefficient r delta physical
            (P.power (index (grid r) k).1) (index (grid r) k).2 : ℂ))
      else none := by
  change (if kept P r k then
    ((P.packet (index (grid r) k).1).map
      (scaleToken ((unit delta physical : ℂ) ^ P.power (index (grid r) k).1))).map
        (scaleToken (normalizedCoefficient r delta physical
          (P.power (index (grid r) k).1) (index (grid r) k).2))
    else none) = _
  by_cases hk : kept P r k
  · rw [if_pos hk, if_pos hk]
    cases P.packet (index (grid r) k).1 with
    | none => rfl
    | some T =>
        simp only [Option.map_some, scale_mul,
          coefficient_cancel r delta physical _ _ hdom]
  · rw [if_neg hk, if_neg hk]

/-- The occupied-row lower floor stays fixed independently of the new
positive cap. It can therefore supply the same clearing power repeatedly. -/
theorem interpolated_lower_bound (P : MarkedPackets D G n S) (r : ℕ)
    (delta physical : ℝ) (bound : ℕ)
    (hfloor : ∀ i T, P.packet i = some T → -(bound : ℤ) ≤ P.power i)
    (k : ℕ)
    (T : Token G n (fun v => (D v).Mood) ((interpolated P r delta physical).rank k))
    (hT : (interpolated P r delta physical).packet k = some T) :
    -(bound : ℤ) ≤ (interpolated P r delta physical).power k := by
  apply lower_bound (retune P (unit delta physical)) r bound
    (normalizedCoefficient r delta physical) _ k T hT
  intro i Q hQ
  obtain ⟨A, hA, _⟩ := Option.map_eq_some_iff.mp hQ
  exact hfloor i A hA

/-- Every occupied copied row has this literal value for all couplings,
including zero. No addition law for integer powers is used here. -/
theorem interpolated_term (P : MarkedPackets D G n S) (r : ℕ)
    (delta physical : ℝ) (hdom : 0 < 1 - delta * physical ^ 2)
    (x : TestSpace D) (g : ℝ) (U : Config G n) (k : ℕ)
    (T : Token G n (fun v => (D v).Mood) (P.rank (index (grid r) k).1))
    (hT : P.packet (index (grid r) k).1 = some T) (hk : kept P r k) :
    (interpolated P r delta physical).term x g U k =
      (g : ℂ) ^ (P.power (index (grid r) k).1 +
          (2 * (index (grid r) k).2.val : ℕ)) *
        ((rowCoefficient r delta physical (P.power (index (grid r) k).1)
          (index (grid r) k).2 : ℂ) * T.read x U) := by
  unfold MarkedPackets.term
  rw [interpolated_packet P r delta physical hdom k, if_pos hk, hT]
  simp only [Option.map_some]
  rw [(interpolated_layout P r delta physical k).2.2.1]
  exact congrArg (fun z : ℂ => (g : ℂ) ^
    (P.power (index (grid r) k).1 + (2 * (index (grid r) k).2.val : ℕ)) * z)
      (scaled_read (rowCoefficient r delta physical
        (P.power (index (grid r) k).1) (index (grid r) k).2 : ℂ) T x U)

private theorem retune_term_factor (P : MarkedPackets D G n S) (a g : ℝ)
    (x : TestSpace D) (U : Config G n) (i : ℕ) :
    (retune P a).term x g U i = (a : ℂ) ^ P.power i * P.term x g U i := by
  rw [retune_term]
  cases hi : P.packet i with
  | none => simp only [MarkedPackets.term, hi, mul_zero]
  | some T =>
      simp only [MarkedPackets.term, hi]
      rw [Complex.ofReal_mul, mul_zpow]
      ring

/-- At the physical point the copied term is a scalar multiple of the
original term at its incoming coupling. The scalar is independent of all
test functions and fields, so this is the literal derivative-transfer inlet. -/
theorem interpolated_term_at_physical (P : MarkedPackets D G n S) (r : ℕ)
    (delta physical : ℝ) (hg : physical ≠ 0) (x : TestSpace D)
    (U : Config G n) (k : ℕ) :
    (interpolated P r delta physical).term x physical U k =
      if kept P r k then
        (normalizedCoefficient r delta physical (P.power (index (grid r) k).1)
          (index (grid r) k).2 *
            (physical : ℂ) ^ (2 * (index (grid r) k).2.val)) *
          P.term x (unit delta physical * physical) U (index (grid r) k).1
      else 0 := by
  change (adaptive (retune P (unit delta physical)) r
    (normalizedCoefficient r delta physical)).term x physical U k = _
  rw [adaptive_term]
  change (if kept P r k then
    (copies (retune P (unit delta physical)) (grid r)
      (normalizedCoefficient r delta physical)).term x physical U k else 0) = _
  by_cases hk : kept P r k
  · rw [if_pos hk, if_pos hk, copies_term _ _ _ physical hg, retune_term]
    rfl
  · rw [if_neg hk, if_neg hk]

variable {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}

private theorem full_copies_paid (P : MarkedPackets D G n S) (r : ℕ)
    (delta physical : ℝ) (hg : physical ≠ 0)
    (hP : P.Paid B address region w (unit delta physical * physical)
      width budget coverOffset coverSlope) :
    (copies (retune P (unit delta physical)) (grid r)
      (normalizedCoefficient r delta physical)).Paid B address region w physical width
        (budget * coefficientMass P.powerCap (grid r)
          (normalizedCoefficient r delta physical) physical) coverOffset coverSlope :=
  copies_paid _ _ _ physical hg (retune_paid P (unit delta physical) physical hP)

/-- The cap-only constant is chosen before the truncation order, the
physical chart parameters, and the packet's field/test values. -/
def paymentConstant (cap : ℕ) : ℝ :=
  Classical.choose (normalized_uniform_bill cap)

theorem paymentConstant_pos (cap : ℕ) : 0 < paymentConstant cap :=
  (Classical.choose_spec (normalized_uniform_bill cap)).1

/-- The complete original Paid budget is multiplied by a leading-one
bound uniform in the row-dependent truncation orders, including zero. -/
theorem interpolated_paid (P : MarkedPackets D G n S) (r cap : ℕ)
    (hcap : P.powerCap ≤ cap) (delta physical : ℝ) (hg : physical ≠ 0)
    (hsmall : |delta * physical ^ 2| ≤ 1 / 2)
    (hP : P.Paid B address region w (unit delta physical * physical)
      width budget coverOffset coverSlope) :
    (interpolated P r delta physical).Paid B address region w physical width
      (budget * (1 + paymentConstant cap * |delta * physical ^ 2|))
        coverOffset coverSlope := by
  apply adaptive_paid_of_bound _ r _ physical hg _
    (by have := paymentConstant_pos cap; positivity) _ (retune_paid P _ physical hP)
  intro e he
  have he' : |e| ≤ (cap : ℤ) := he.trans (by exact_mod_cast hcap)
  exact (Classical.choose_spec (normalized_uniform_bill cap)).2
    e he' delta physical hg hsmall r

/-- Exact physical read of every original test tuple and full field.
The actual Paid receipt supplies the summability of the copied series. -/
theorem interpolated_at_physical [Fintype V] (P : MarkedPackets D G n S)
    (r : ℕ) (delta physical : ℝ) (hg : physical ≠ 0)
    (hdom : 0 < 1 - delta * physical ^ 2)
    (hP : P.Paid B address region w (unit delta physical * physical)
      width budget coverOffset coverSlope) (x : TestSpace D) (U : Config G n) :
    (interpolated P r delta physical).read x physical U =
      P.read x (unit delta physical * physical) U := by
  rw [interpolated, adaptive_read_eq _ r _
    (normalizedCoefficient_zero r delta physical)]
  rw [copies_read_of_scalar _ _ _ physical hg
    (fun e _ => normalized_at_physical r delta physical e hg hdom) x U
      (NativePaidPacketColors.read_summable
        (full_copies_paid P r delta physical hg hP) hg x physical U)]
  exact retune_read P _ physical x U

/-- The full original-fibre formula away from zero. RFI's cleared contact
uses this identity there and the literal shifted-power rows at zero. -/
theorem interpolated_read [Fintype V] (P : MarkedPackets D G n S)
    (r : ℕ) (delta physical : ℝ) (hphysical : physical ≠ 0)
    (hdom : 0 < 1 - delta * physical ^ 2)
    (hP : P.Paid B address region w (unit delta physical * physical)
      width budget coverOffset coverSlope)
    (x : TestSpace D) (g : ℝ) (hg : g ≠ 0) (U : Config G n) :
    (interpolated P r delta physical).read x g U =
      ∑' i, Poly.send (P.mode i)
        ((corrected (P.power i) delta physical
          (retuningOrder r (P.power i)) g : ℂ) * P.term x g U i) := by
  rw [interpolated, adaptive_read_eq _ r _
    (normalizedCoefficient_zero r delta physical)]
  rw [copies_read _ _ _ g hg x U
    (NativePaidPacketColors.read_summable
      (full_copies_paid P r delta physical hphysical hP) hphysical x g U)]
  apply tsum_congr
  intro i
  simp_rw [retune_term_factor]
  apply Marker.Poly.ext
  intro a
  simp only [Poly.part_sum, Poly.part_send]
  by_cases ha : a = P.mode i
  · simp only [retune, ha, if_pos]
    rw [← Finset.sum_mul, normalized_sum]
    have hu : (unit delta physical : ℂ) ^ P.power i ≠ 0 :=
      zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr (unit_nonzero delta physical hdom))
    calc
      _ = (((unit delta physical : ℂ) ^ P.power i)⁻¹ *
          (unit delta physical : ℂ) ^ P.power i) *
            ((corrected (P.power i) delta physical
              (retuningOrder r (P.power i)) g : ℂ) * P.term x g U i) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hu, one_mul]
  · simp only [retune, if_neg ha, Finset.sum_const_zero]

end YM.Integration.ActualPacketInterpolatedRetuning
end
