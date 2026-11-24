import YM.Integration.WilsonLimitConstruction.FundedPhysicalCatalogue
import YM.Integration.WilsonLimitConstruction.FundedCoefficientPrior
import YM.Integration.SelectedPlanKineticDenominator
import YM.Integration.ActualInputGroundPrice

/-! The signed finite-position discrepancy in the independently prescribed
cover model contributes to the measured kinetic coefficient on the true bond. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedCoverKineticMeasurement
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} (T : Run G)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {J : Request V} {A : NumericSchedule T.family J}
    {d : LocalFormal.Datum T.family R} {caps : Handoff.OutputCapacities} {K : NumericPrices A}
    (Y : Bulk.Chain T.family.path) (F : AnalyticInput J A d) (M : FundedPhysicalCatalogue.Purchase caps K F)

def ground (x : TestSpace J.tests) (e : ℕ) (B : fieldDir G (T.family.side d.level d.period) 1) : ℂ :=
  Symmetry.Orbit.ground (d.kernel Y) (RG08.Line.green (T.family.path.levels.clock.op d.level d.period))
    d.tag (F.colors x) J.order (e+2) B -
  Symmetry.Orbit.ground (d.kernel Y) (RG08.Line.green (T.family.path.levels.clock.op d.level d.period))
    d.tag (F.colors x) J.order (e+2) 0

/-- This is the literal centered finite-minus-cover coefficient on the
original regulated torus; the definition does not assert its smallness. -/
def difference (x : TestSpace J.tests) (e : ℕ) (B : fieldDir G (T.family.side d.level d.period) 1) : ℂ :=
  -ground T Y F x e B -
  (jet (SelectedPlanClearedNumerator.numerator T M.plan d.level) (e+4) (1,B)-
   jet (SelectedPlanClearedNumerator.numerator T M.plan d.level) (e+4) (1,0))

def Tested (hG : G.Simple) (x : TestSpace J.tests) : Prop :=
  ∀ e : ℕ, e≤J.order-2 → ‖difference T Y F M x e
    (NativeNormalizedBondTest.actualField T hG d.level d.period)‖ ≤ 1

theorem position (x : TestSpace J.tests) (e : ℕ) (he : e≤J.order-2)
    (B : fieldDir G (T.family.side d.level d.period) 1) :
    ((M.plan.coefficient d.level e *
      jet (SelectedPlanTriangular.kinetic (N:=d.cutoff) (period:=d.period) T d.level) 2 B : ℝ):ℂ) =
      -ground T Y F x e B-FundedCoefficientPrior.centered T M.plan d.level e B-
        difference T Y F M x e B := by
  have hB := SelectedPlanTriangular.coefficient T M.plan d.level M.vacuum e he d.below.le
    (A.output_width_pos d.level) B
  have h0 := SelectedPlanTriangular.coefficient T M.plan d.level M.vacuum e he d.below.le
    (A.output_width_pos d.level) 0
  have hz : jet (SelectedPlanTriangular.kinetic (N:=d.cutoff) (period:=d.period) T d.level) 2 0=0 := by
    unfold jet
    rw [(iteratedFDeriv ℝ 2 (SelectedPlanTriangular.kinetic (N:=d.cutoff)
      (period:=d.period) T d.level) 0).map_coord_zero (0:Fin 2) rfl,smul_zero]
  rw [hz,mul_zero,Complex.ofReal_zero,sub_eq_zero] at h0
  rw [←hB]
  unfold difference FundedCoefficientPrior.centered
  rw [h0]
  abel

theorem bound (hG : G.Simple) (hT : ActualRunNativeComponentRecipe.Attached T)
    (x : TestSpace J.tests) (e : ℕ) (he : e≤J.order-2) (hm : 0<d.level) :
    let B := NativeNormalizedBondTest.actualField T hG d.level d.period
    |M.plan.coefficient d.level e| ≤ 2*((Fintype.card (TypeFace 2):ℝ)*Real.log (T.family.path.levels.clock.hatBeta (d.level-1))) *
      (‖ground T Y F x e B‖+‖FundedCoefficientPrior.centered T M.plan d.level e B‖+‖difference T Y F M x e B‖) := by
  dsimp only
  let B := NativeNormalizedBondTest.actualField T hG d.level d.period
  let q := jet (SelectedPlanTriangular.kinetic (N:=d.cutoff) (period:=d.period) T d.level) 2 B
  obtain ⟨hq,paid⟩ := SelectedPlanKineticDenominator.denominator T hG hT d.cutoff d.level d.period d.below hm
  change 0<q at hq
  change q⁻¹ ≤ _ at paid
  have h := congrArg norm (position T Y F M x e he B)
  have hk : ‖((M.plan.coefficient d.level e*q:ℝ):ℂ)‖ = abs (M.plan.coefficient d.level e) * q := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos hq]
  rw [hk] at h
  let a := ground T Y F x e B
  let b := FundedCoefficientPrior.centered T M.plan d.level e B
  let c := difference T Y F M x e B
  have debt : abs (M.plan.coefficient d.level e) * q ≤ (‖a‖+‖b‖)+‖c‖ := by
    calc _ = ‖(-a-b)-c‖ := h
         _ ≤ ‖-a-b‖+‖c‖ := norm_sub_le (-a-b) c
         _ ≤ (‖-a‖+‖b‖)+‖c‖ := add_le_add (norm_sub_le (-a) b) le_rfl
         _ = _ := by rw [norm_neg]
  have rearrange : abs (M.plan.coefficient d.level e) = q⁻¹ * (abs (M.plan.coefficient d.level e) * q) := by
    rw [mul_comm _ q,←mul_assoc,inv_mul_cancel₀ hq.ne',one_mul]
  rw [rearrange]
  exact (mul_le_mul_of_nonneg_left debt (inv_nonneg.mpr hq.le)).trans
    (mul_le_mul_of_nonneg_right paid (add_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b)) (norm_nonneg c)))

end YM.Integration.WilsonLimitConstruction.FundedCoverKineticMeasurement
end
