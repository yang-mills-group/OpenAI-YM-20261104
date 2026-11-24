import YM.Integration.WilsonOriginalRecroppedShapeJets
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! Identify the absolutely summable signed series with the actual continuous
localized jet on a periodized real compact box. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFourierReadback
open Filter Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb UnitAddTorus
open scoped Topology BigOperators
open WilsonOriginalTestedFourierBank (Prices)
open WilsonOriginalLowFourierJets (jet)
open WilsonOriginalSignedTailSum (remainder)

/-- The same radius works for all points of the whole box. The input
identifies the Fourier coefficient of the genuine localized derivative;
Fourier inversion here uses the summability earned at the requested crop. -/
theorem original {G : Gauge} {warm : ℝ → ℝ} (hG : G.Simple) (paid : Coupling G warm)
    {d j : ℕ} {read : ℝ → (Fin d → ℤ) → ℂ} {coeff : ℕ → (Fin d → ℤ) → ℂ}
    (b : Prices warm read coeff) (p : ℕ) (axis : Fin j → Fin d) (unit : Fin j → ℂ)
    (actual : ℝ → C(UnitAddTorus (Fin d),ℂ))
    (filed : ∀ᶠ r : ℝ in trail, ∀ v, mFourierCoeff (actual r) v =
      jet axis unit v * remainder (warm r) p (read r) coeff v)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in trail, ∀ x, ‖actual r x‖ ≤ ε*warm r^p := by
  have purchased := WilsonOriginalRecroppedShapeJets.original hG paid b p axis unit hε
  filter_upwards [purchased,filed] with r series same x
  have total : Summable (mFourierCoeff (actual r)) := by
    have all := (series (fun _ => 1) (fun _ => (norm_one (α := ℂ)).le)).1
    simpa only [one_mul, ← same] using all
  let phase := fun v : Fin d → ℤ => mFourier v x
  have normPhase (v) : ‖phase v‖ ≤ 1 :=
    ((mFourier v).norm_coe_le_norm x).trans_eq mFourier_norm
  have value := (hasSum_mFourier_series_apply_of_summable total x).tsum_eq
  have returned : (∑' v,phase v*jet axis unit v*remainder (warm r) p (read r) coeff v) =
      actual r x := by
    rw [← value]
    apply tsum_congr
    intro v
    rw [same]
    change _ = (jet axis unit v*remainder (warm r) p (read r) coeff v)*phase v
    ring
  simpa only [returned] using (series phase normPhase).2

end YM.Integration.WilsonOriginalFourierReadback

