import YM.Integration.WilsonWindowReportingPace
import YM.Integration.WilsonMeasuredWindow
import YM.PhysMS.Foundation.Estimates

/-! Cover every sufficiently small physical radius by the original
first-crossing reporting level on the funded slow-block path. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFundedMeasuredWindow

open Filter Function Lattice RG Wilson MergeProof OPE Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology

private theorem slower {b x : ℝ} (hb : 2 ≤ b) (hx : 0 ≤ x)
    (h : b ≤ Real.log (2+x)) : b ≤ x := by
  have two : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have rest : b ≤ Real.exp (b-1) := by linarith only [Real.add_one_le_exp (b-1)]
  have grow : b+2 ≤ Real.exp b := calc
    b+2 ≤ 2*b := by linarith only [hb]
    _ ≤ Real.exp 1 * Real.exp (b-1) := mul_le_mul two rest (by linarith only [hb]) (Real.exp_pos 1).le
    _ = Real.exp b := by rw [← Real.exp_add]; congr 1; ring
  have upper := (Real.le_log_iff_exp_le (by linarith only [hx] : 0 < 2+x)).mp h
  linarith only [grow,upper]

variable {G : Gauge} (R : Run G) (slow : WilsonWindowReportingPace.Slow R.kit)
include slow

theorem paced (m : ℕ) : ((R.family.S.block m).val : ℝ) ≤
    WilsonAdmissionScale.logarithm R.family.path.levels m := by
  have large : 2 ≤ (R.family.S.block m).val := by have h := R.family.S.block_large m; omega
  exact slower (by exact_mod_cast large)
    (Real.log_nonneg (R.family.path.levels.fits.delayed m).le) (slow.2 m)

variable (hG : G.Simple) {B : ℕ} (hB : 0 < B)
include hB

theorem all_radii :
    let A := R.family.path.levels
    let m := WilsonMeasuredWindow.stop A hG B
    Tendsto m (𝓝[>] (0 : ℝ)) atTop ∧ ∀ r : ℝ, 0 < r → r ≤ R.family.S.a 0 →
      RG16.Lambda A (m r)^B ≤ r / R.family.S.a (m r) ∧
      r / R.family.S.a (m r) ≤ RG16.Lambda A (m r)^(B+1) := by
  dsimp only
  refine ⟨WilsonMeasuredWindow.stop_tendsto R.family.path.levels hG B hB,?_⟩
  intro r hr hs
  let A := R.family.path.levels
  let m := WilsonMeasuredWindow.stop A hG B r
  have apos := R.family.S.a_pos m
  obtain ⟨lo,hi⟩ := WilsonMeasuredWindow.window A hG B (paced R slow) hB hr hs
  constructor
  · apply (le_div_iff₀ apos).2
    simpa only [WilsonMeasuredAdmission.mast,WilsonAdmissionScale.logarithm,RG16.Lambda,mul_comm] using lo
  · apply (div_le_iff₀ apos).2
    simpa only [WilsonMeasuredAdmission.mast,WilsonAdmissionScale.logarithm,RG16.Lambda,mul_comm] using hi

theorem between {b j : ℝ → ℕ} {a c : ℝ}
    (lb : Height R.family.S trail LogV b a) (lj : Height R.family.S trail LogV j c)
    (ha : a < 1) (hc : 1 < c) :
    ∀ᶠ r in trail, b r < WilsonMeasuredWindow.stop R.family.path.levels hG B r ∧
      WilsonMeasuredWindow.stop R.family.path.levels hG B r < j r := by
  have live : Height R.family.S trail LogV (WilsonMeasuredWindow.stop R.family.path.levels hG B) 1 :=
    WilsonMeasuredWindow.measured_stop_height R.family.path.levels hG B (paced R slow) hB
      PhysMS.to_log_zoom PhysMS.length_rate
  exact (lb.earlier ha PhysMS.to_log_zoom live).and (live.earlier hc PhysMS.to_log_zoom lj)

end YM.Integration.WilsonFundedMeasuredWindow
end

