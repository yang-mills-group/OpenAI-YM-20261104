import YM.RG05Readout.Many.Iota
import YM.Integration.WilsonFundedMeasuredWindow

/-! The original coarse enclosing cell of a physical radius on the funded schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCloseCaptureDate
open Filter Lattice OPE OPE.Log Trace.Pilot PhysicalNext.Repeat.Legato
open scoped Classical Topology

def level (S : Schedule) (r : ℝ) : ℕ := RG05Readout.crossLevel S r - 1

theorem bracket (S : Schedule) {r : ℝ} (hr : 0 < r) (hs : r ≤ S.a 0) :
    S.a (level S r + 1) < r ∧ r ≤ S.a (level S r) := by
  let h : ∃ i : ℕ, -Real.log r < S.scale i := (S.divergent.eventually_gt_atTop _).exists
  let n := Nat.find h
  have hi : -Real.log r < S.scale n := Nat.find_spec h
  have ha (i : ℕ) : Real.log (S.a i) = -S.scale i := by simp [Schedule.scale]
  have pos : 0 < n := by
    by_contra! hz
    rw [show n = 0 by omega] at hi
    have := Real.log_le_log hr hs
    rw [ha] at this
    linarith
  change S.a (n-1+1) < r ∧ r ≤ S.a (n-1)
  have prev : S.scale (n-1) ≤ -Real.log r := not_lt.mp (Nat.find_min h (show n-1 < n by omega))
  rw [show n-1+1=n by omega]
  constructor
  · apply (Real.log_lt_log_iff (S.a_pos _) hr).mp
    rw [ha]
    linarith
  · apply (Real.log_le_log_iff hr (S.a_pos _)).mp
    rw [ha]
    linarith

theorem identifies (S : Schedule) {r : ℝ} {b : ℕ}
    (left : S.a (b+1) < r) (right : r ≤ S.a b) : level S r = b := by
  obtain ⟨l,h⟩ := bracket S ((S.a_pos _).trans left) (right.trans (S.strictAnti.antitone (Nat.zero_le _)))
  apply le_antisymm
  · by_contra! z
    exact (not_lt_of_ge (h.trans (S.strictAnti.antitone z))) left
  · by_contra! z
    exact (not_lt_of_ge (right.trans (S.strictAnti.antitone z))) l

variable {G : Gauge} (R : Run G)

theorem height : Height R.family.S trail LogV (level R.family.S) 1 := by
  have := RG05Readout.pace_crossing R.family.path.levels.fits.mesh PhysMS.to_log_zoom PhysMS.length_rate
  exact Log.previous PhysMS.to_log_zoom this.1 R.family.path.levels.fits.mesh

theorem window (slow : WilsonWindowReportingPace.Slow R.kit) (hG : G.Simple)
    {B : ℕ} (hB : 0 < B) {r : ℝ} (hr : 0 < r) (hsmall : r ≤ R.family.S.a 0) :
    let A := R.family.path.levels
    let b := level R.family.S r
    let m := WilsonMeasuredWindow.stop A hG B r
    b < m ∧ R.family.S.a (b+1) < r ∧ r ≤ R.family.S.a b ∧
      R.family.S.a b / R.family.S.a m ≤ RG16.Lambda A m ^ (B+2) ∧
      ((m-b:ℕ):ℝ) ≤ R.family.S.scale m - R.family.S.scale b ∧
      R.family.S.scale m - R.family.S.scale b ≤ ((B+2:ℕ):ℝ)*Real.log (RG16.Lambda A m) := by
  dsimp only
  let S := R.family.S
  let A := R.family.path.levels
  let m := WilsonMeasuredWindow.stop A hG B r
  let b := level S r
  obtain ⟨left,right⟩ := bracket S hr hsmall
  have bm : b < m := WilsonMeasuredWindow.before_stop A hG B hB hr b right
  have ratio : S.a b / S.a m ≤ RG16.Lambda A m ^ (B+2) :=
    WilsonMeasuredWindow.ratio_le A hG B (WilsonFundedMeasuredWindow.paced R slow) hB hr b right left
  refine ⟨bm,left,right,ratio,RG05Readout.Many.tall (C:=R.family) _ _ bm.le,?_⟩
  have upper := Real.log_le_log (div_pos (S.a_pos b) (S.a_pos m)) ratio
  rw [Real.log_div (S.a_pos b).ne' (S.a_pos m).ne', Real.log_pow] at upper
  have ha (i : ℕ) : Real.log (S.a i) = -S.scale i := by simp [Schedule.scale]
  rw [ha, ha] at upper
  change S.scale m - S.scale b ≤ _
  linarith only [upper]

end YM.Integration.WilsonCloseCaptureDate
