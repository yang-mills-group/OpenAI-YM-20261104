import YM.Integration.FVA1Physical.Sources.Round2.CrossingTail
import YM.LocalLTE.Dilation.Reserve

/-! Quantitative cancellation for forced terms actually built by the exact
mask-reattachment operation. Other external flags and their absolute number
never appear in the estimate after division by the original vacuum. -/

namespace YM.Integration.FVA1Physical.Round2

open Lattice RG Wilson Source Push Push.Local Push.AbsoluteSums MergeProof LocalLTE.Dilation
open Planned.GuardedAtom.Guard
open scoped BigOperators Classical

variable {G : Gauge} {n : Side}

/-- All anchored failed terms on a healthy collar are in the support tail.
The hypothesis on these terms is the compiler's reserved-support budget. -/
theorem attached_sum_tail (P : Rep G n) (X : ℕ → Support n) (f : ℕ → Config G n → ℂ)
    (a : ℕ → ℝ) {o : Site n} (ho : ∀ i, o ∈ X i)
    (hflag : ∀ i, Attaches P.p.threshold (X i) (f i))
    (ha : ∀ i, 0 ≤ a i ∧ ∀ v, ‖f i v‖ ≤ a i) {V : ℝ}
    (hcost : SumBudget (fun i => reservedMass P.p (X i) (a i)) V)
    (S : Support n) (hs : o ∈ S) (v : Config G n) (r : ℕ)
    (hgood : Healthy P.p.threshold (halo (r*GridApprox.Attach.leg P.p.B) S) v) :
    ‖∑' i, f i v‖ ≤ Real.exp (-(P.p.supportExponent+2) * r) * V := by
  let e := P.p.supportExponent+2
  have he : 0 ≤ e := add_nonneg P.p.exponent_pos.le zero_le_two
  have hmajor := budget_scale (Real.exp_pos (-e*r)).le hcost
  have hsum : SumBudget (fun i => ‖f i v‖) (Real.exp (-e*r)*V) := by
    apply budget_mono hmajor (fun _ => norm_nonneg _)
    intro i
    by_cases hzero : f i v = 0
    · rw [hzero, norm_zero]
      exact mul_nonneg (Real.exp_pos _).le (hcost.1 i)
    have hbad : ¬ Healthy P.p.threshold (X i) v := fun h => hzero ((hflag i).healthy_zero v h)
    obtain ⟨z, hz, hz'⟩ := Finset.not_disjoint_iff.mp hbad
    have hcov := LocalLTE.Sail.Round2.cover_of_flag_outside (ho i) hs hz
      (show z ∉ halo (r*GridApprox.Attach.leg P.p.B) S from fun h => Finset.disjoint_left.mp hgood h hz')
    change _ ≤ Real.exp (-e * r) * (Real.exp (e * coverNumber P.p.B (X i)) * a i)
    rw [← mul_assoc, ← Real.exp_add]
    apply (ha i).2 v |>.trans (le_mul_of_one_le_left (ha i).1 _)
    apply Real.one_le_exp
    nlinarith only [mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcov : (r:ℝ) ≤ _) he]
  exact (norm_tsum_le_tsum_norm hsum.2.1).trans hsum.2.2

/-- Dilation.cover produces the normalizing factor itself. Consequently the
same support-tail bound applies to the *relative full gas contribution*,
including its complete exterior and the actual conditional denominator. -/
theorem normalized_rented_crossing (P : Rep G n) (X : ℕ → Support n)
    (labels : Berths P.p P.activities X) (f : ℕ → Config G n → ℂ) (a : ℕ → ℝ)
    {o : Site n} (ho : ∀ i, o ∈ X i) (hflag : ∀ i, Attaches P.p.threshold (X i) (f i))
    (ha : ∀ i, 0 ≤ a i ∧ ∀ v, ‖f i v‖ ≤ a i) {V σ C Λ δ w : ℝ}
    (hcost : SumBudget (fun i => reservedMass P.p (X i) (a i)) V)
    (hP : P.Lawful σ C Λ δ w) (hw : 0 ≤ w) (hwidth : hitWidth P.p * w ≤ 1)
    (S : Support n) (hs : o ∈ S) (v : Config G n) (hp : 0 < P.eval v) (r : ℕ)
    (hgood : Healthy P.p.threshold (halo (r*GridApprox.Attach.leg P.p.B) S) v) :
    ‖(Real.exp (P.exponent v):ℂ) * (∑' rows, gasMark P.p P.activities v rows (rented labels f)) /
        (P.eval v : ℂ)‖ ≤ Real.exp (-(P.p.supportExponent+2)*r)*V := by
  obtain ⟨_, _, _, _, hsum⟩ := cover labels f hflag ho a ha hcost hP hw hwidth
  have hnorm : (Real.exp (P.exponent v):ℂ) * (∑' rows, gasMark P.p P.activities v rows (rented labels f)) /
      (P.eval v : ℂ) = ∑' i, f i v := by
    apply (div_eq_iff (Complex.ofReal_ne_zero.mpr hp.ne')).mpr
    rw [(hsum v).tsum_eq, Rep.eval, Complex.ofReal_mul]
    ring
  rw [hnorm]
  exact attached_sum_tail P X f a ho hflag ha hcost S hs v r hgood

end YM.Integration.FVA1Physical.Round2
