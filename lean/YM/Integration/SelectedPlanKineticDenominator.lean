import YM.Integration.SelectedPlanGroundTriangle
import YM.Integration.NativeNormalizedBondTest
import YM.Integration.ActualRunNativeComponentRecipe
import YM.Integration.RunRG02Along

/-! The original constructed Run supplies a positive kinetic denominator on
one explicit unit bond field. The same selected Plan's coefficient is then
bounded by its centered ground and earlier-coefficient numerator. The native
postnumeric payment is consumed from the retained construction, not assumed
as a new Account or prediction estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedPlanKineticDenominator
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} (T : Run G) (hG : G.Simple)

/-- Original path, original postnumeric payment, and an explicit one-bond test. -/
theorem denominator (hT : ActualRunNativeComponentRecipe.Attached T)
    (N m period : ℕ) (hm : m < N) (hm0 : 0 < m) :
    let B := NativeNormalizedBondTest.actualField T hG m period
    let J := jet (SelectedPlanTriangular.kinetic (N := N) (period := period) T m) 2 B
    0 < J ∧ J⁻¹ ≤ 2 * ((Fintype.card (TypeFace 2) : ℝ) *
      Real.log (T.family.path.levels.clock.hatBeta (m - 1))) := by
  obtain ⟨s, Q, C, n, _hbase, _hfloor, _hsheet, hquote,
    _hnum, _hpost, _hstage, hReal⟩ := hT
  have hpay := hReal.payment
  rw [← hquote] at hpay
  have hb := T.alloy.B.support.cap N m hm.le
  have ht := T.alloy.B.support.links N m hm.le
  rw [← CommonConstruction.runAlong_actual_path T N m period hm.le] at hb ht
  have hs := ((CommonConstruction.runAlong T).home
    (RG08.Line.green (T.family.path.levels.clock.op m period)) hm).2.2.2.1
  have hi : m - 1 < N := by omega
  have he : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  have hb' : (T.family.path.rep N period m).path.Bounds
      (T.family.path.levels.params (m - 1 + 1)).clip
      (T.family.path.levels.params m).width
      (T.family.path.levels.params m).paths
      (T.family.path.levels.clock.loopCap m) := by
    rw [he]
    exact hb
  have ht' : Attached (T.alloy.B.M.H N (m - 1 + 1))
      (T.family.path.rep N period m).path := by simpa only [he] using ht
  have hs' : Bid.Sworn (T.alloy.B.M.H N (m - 1 + 1))
      (T.family.side m period) G := by
    rw [he]
    exact hs
  have h := NativeNormalizedBondTest.paid_main_jet hG T.alloy.B.plan hpay
    N (m - 1) hi (T.family.side m period)
    (NativeNormalizedBondTest.actual_size T m period) hb' ht' hs'
  dsimp only at h
  rw [he] at h
  exact h

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} {A : NumericSchedule T.family J}
    {datum : LocalFormal.Datum T.family R}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain T.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum}

/-- No income estimate is an input: the right side is the exact original
centered ground and same-list prior numerator, with a paid denominator. -/
theorem coefficient_bound (hT : ActualRunNativeComponentRecipe.Attached T)
    (hm0 : 0 < datum.level) (M : AnalyticOutput caps Y K F)
    (x : TestSpace J.tests) (e : ℕ) (he : e ≤ J.order - 2) :
    let B := NativeNormalizedBondTest.actualField T hG datum.level datum.period
    |M.plan.coefficient datum.level e| ≤
      (2 * ((Fintype.card (TypeFace 2) : ℝ) *
        Real.log (T.family.path.levels.clock.hatBeta (datum.level - 1)))) *
      (‖Symmetry.Orbit.ground (datum.kernel Y)
          (RG08.Line.green (T.family.path.levels.clock.op datum.level datum.period))
          datum.tag (F.colors x) J.order (e + 2) B -
        Symmetry.Orbit.ground (datum.kernel Y)
          (RG08.Line.green (T.family.path.levels.clock.op datum.level datum.period))
          datum.tag (F.colors x) J.order (e + 2) 0‖ +
        ‖SelectedPlanGroundTriangle.priorCentered T M e B‖) := by
  dsimp only
  let B := NativeNormalizedBondTest.actualField T hG datum.level datum.period
  let q := jet (SelectedPlanTriangular.kinetic (N := datum.cutoff)
    (period := datum.period) T datum.level) 2 B
  obtain ⟨hq, hpaid⟩ := denominator T hG hT datum.cutoff datum.level
    datum.period datum.below hm0
  change 0 < q at hq
  change q⁻¹ ≤ _ at hpaid
  have hid := SelectedPlanGroundTriangle.coefficient_green T M x e he B
  have hnorm := congrArg norm hid
  have hleft : ‖((M.plan.coefficient datum.level e * q : ℝ) : ℂ)‖ =
      |M.plan.coefficient datum.level e| * q := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hq]
  rw [hleft] at hnorm
  have hbound := hnorm.trans_le (norm_sub_le _ _)
  have heq : |M.plan.coefficient datum.level e| =
      q⁻¹ * (|M.plan.coefficient datum.level e| * q) := by
    rw [mul_comm _ q, ← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hq.le)).trans
    (mul_le_mul_of_nonneg_right hpaid (add_nonneg (norm_nonneg _) (norm_nonneg _)))

end YM.Integration.SelectedPlanKineticDenominator
end
