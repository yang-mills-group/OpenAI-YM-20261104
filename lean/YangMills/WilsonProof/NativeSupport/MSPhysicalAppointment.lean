import YangMills.PerturbativeMatching.PositionFrame
import YangMills.WilsonProof.NativeSupport.MatchingSpec
import MSPositionPrescription
import MSPositionScreens
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
import YangMills.WilsonProof.NativeSupport.MSPositionLabels
import MSNumericalAdjustment

/-! The measured coupling and fields come from one physical hierarchy. The
finite tests, the signed triangle and the Taylor coefficients used to adjust
the fields are supplied by the independent position prescription. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.MSbar

open Filter MeasureTheory
open scoped Topology BigOperators Classical

variable {g : GaugeGroup}

variable {B : Maxwell.Reference g} {C : WilsonFamily g} (T : Hierarchy C)









/-- Measure the signed connected (6,4,4) triangle before adjusting the
fields. Both matching tests use this exact clock and the same adjusted
frame on the same Wilson hierarchy. -/
def appointed (P : PositionPrescription B) {N : (d k : ℕ) → Module.End ℂ (B.sector d)}
    (L : NumericalAdjustment B N) (C : WilsonFamily g) (T : Hierarchy C)
    (H : Matching.Measurement B T) : Prop :=
  ∃ J : PositionFrames T B,
    PositionNormalized T P J ∧ PositionLocallyUnique T P J ∧
    PositionUnital T J ∧ PositionNested T J ∧ PositionReal T J ∧
    (∀ᶠ s : ℝ in 𝓝[>] 0,
      let m := positionMoment T J s 6 (n := 3)
      Integrable (fun x => P.triangle.profile x * P.triangle.connected m x) ∧
      H.clock s = P.triangle.measure m / P.triangle.cT) ∧
    ∀ d, ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v, H.frame s d v = J s d (L.value d (H.clock s) v)

/-- The final field frame used in the correlation and OPE comparisons has
the same Euclidean reality property as the position-normalized frame. -/
theorem appointed_positionReal {P : PositionPrescription B}
    {N : (d k : ℕ) → Module.End ℂ (B.sector d)}
    {L : NumericalAdjustment B N} {H : Matching.Measurement B T}
    (h : appointed P L C T H) : PositionReal T H.frame := by
  obtain ⟨J, _, _, _, _, realJ, _, agree⟩ := h
  intro d
  filter_upwards [realJ d, agree d, H.positive] with s atLength fields positive
  intro n v hv x hx
  simp only [fields]
  exact atLength n (fun i => L.value d (H.clock s) (v i))
    (fun i => L.real (H.clock s) positive d (v i) (hv i)) x hx

end YangMills.MSbar
