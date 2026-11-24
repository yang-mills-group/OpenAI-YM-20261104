import YM.Integration.WilsonMeasuredOnlyHard
import YM.Integration.WilsonOriginalDepositedHardTable

/-! The sole forced part of a measured coefficient as a tested addition to
the original hard income, with its original denominator and quiet partners. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredForcedIntake
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker Overlay QuadraticLocal Ac
open Push.Corrected Push.AbsoluteSums QuadraticLocal.Fusion.Attached MergeProof.Accent
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonOriginalDepositedHard
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} {A : Hol G}
  {P W : Rep G n} {V T : Type} [Fintype V] [DecidableEq V] {J : Census V} {o : V → Site n}

/-- The old marked slate may already have any mixed entries.  Its fired
coordinate is subtracted with exactly the same complete cover sum. -/
theorem original (prior : Hard T W.p W.activities.forced W.activities.K o J) (j : V)
    (q : Coefficient F n) (law : q.Format (o j) A W) (t : T → ℂ)
    (w : V → ℝ) (hw : ∀ i, 0<w i) {κ M k : ℝ}
    (old : prior.Paid w W.p.B W.p.supportExponent k) (bounded : ∀ a, ‖t a‖≤1)
    (actual : q.remBound (o j) W κ M)
    (same : P.p=W.p) (quiet : W.eval=P.eval) (owners : P.activities.forced=W.activities.forced)
    (S : SectionData F) :
    (joined prior j q law t).Paid w W.p.B W.p.supportExponent (k+w j*(κ*M)) ∧
    (∀ x b U,
      (packet W.activities W.p ((joined prior j q law t).hard x) U b).part (J.fire j) -
        (packet W.activities W.p (prior.hard x) U b).part (J.fire j)=t x*q.marked W b U) ∧
    ∀ x U,t x*q.density (o j) S W U=t x*(soft q).density (o j) S P U+
      (Real.exp (W.exponent U):ℂ)*
      ((∑' b,packet W.activities W.p ((joined prior j q law t).hard x) U b).part (J.fire j) -
       (∑' b,packet W.activities W.p (prior.hard x) U b).part (J.fire j)) :=by
  refine ⟨paid prior j q law t w hw old bounded actual,
    fun x b U=>WilsonOriginalDepositedHardTable.inventory prior j q law t x U b,?_⟩
  intro x U
  rw [WilsonOriginalDepositedHardTable.full prior j q law t w hw old bounded actual x U,
    (WilsonMeasuredOnlyHard.original q P W same quiet owners S A (o j) κ M law actual).2.2.1 U]
  unfold account
  ring

end YM.Integration.WilsonMeasuredForcedIntake
