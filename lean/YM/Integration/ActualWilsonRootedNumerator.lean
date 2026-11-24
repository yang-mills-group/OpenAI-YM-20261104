import YM.Integration.ActualWilsonSpectatorNumerator
import YM.Integration.KBoundGas
import YM.SectorNext.VACUUM_NORMALIZATION.Covered

/-! Original support-weighted signed numerator with the genuine flag decay. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonRootedNumerator
open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Extra.Histories Trace.Physical Trace.Physical.GermGraph
open ActualWilsonAxisSpectator SectorNext.Vacuum Push.AbsoluteSums
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

theorem vacuum (W : Rep G n) {w : ℝ} (hw : w ≤ 1) (H : W.activities.KBound W.p w)
    (U : Config G n) : ‖W.activities.gas W.p U‖ ≤ (if flags W.p.threshold U=∅ then 1 else w) *
      Real.exp (-flagRate W.p * (flags W.p.threshold U).card) :=
  (norm_tsum_le_tsum_norm (Activities.gasOccurrence_absolute_of_KBound H U)).trans
    (gas_cover W.activities hw H U)

theorem selected (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    (S : Chosen K I M) {δ : ℝ} {a : ℕ} (H : Bounds S δ a)
    (hFine : I.carrier.rep.eval=(R.family.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (hLate : ActualSelectedCofactorFunding.start R.family hG R.makes (Fintype.card V) ≤ datum.level)
    (hres : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (x : IndependentTests J.tests) (v : V) (U : Config G (R.family.side datum.level datum.period)) :
    let C := R.family
    let i := datum.level
    let P := C.path.levels.budget i
    let W := C.path.rep datum.cutoff datum.period i
    let X := S.output.carrier.rep
    let w := C.path.levels.clock.forcedAllowance i
    let g := Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (i+1)
    let fee := forcedDivisor C i*(F.kernelCosts v*g^a/F.outputRadii v)
    let e := ActualWilsonForcedSlots.address X (OriginalForcedAddresses.actual_keeper R hG
      datum.cutoff i datum.period datum.below.le)
    let row j := ((S.output.residual.leaf (testInclusion J.tests x)).contents.each j U).part (B.fire v) *
      ((Real.exp (X.exponent U) : ℂ)*dressed X j U-(Real.exp (W.exponent U) : ℂ)*dressed W (e j) U)
    let t := (X.activities.gas X.p U : ℂ)*(Real.exp (-W.exponent U) : ℂ)
    let cap := 2*w*Real.exp (-flagRate P * (flags P.threshold U).card)*fee
    SumBudget (fun j => X.p.mass (X.activities.forced j).support ‖t*row j‖) cap ∧
      ‖t*spectator R hG S x v U‖ ≤ cap := by
  intro C i P W X w g fee e row t cap
  let b := Real.exp (X.exponent U)+Real.exp (W.exponent U)
  let vcap := Real.exp (-flagRate P * (flags P.threshold U).card)
  have hs := (ActualWilsonSpectatorBudget.selected R hG S H hLate hres x v U).1
  change SumBudget (fun j => X.p.mass (X.activities.forced j).support ‖row j‖) (b*fee) at hs
  have hf : 0 ≤ fee := by
    by_contra! h
    exact (not_lt_of_ge (budget_nonneg hs)) (mul_neg_of_pos_of_neg (add_pos (Real.exp_pos _) (Real.exp_pos _)) h)
  have hw : w ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
  have hx : X.p=P := S.output.carrier.point
  have hy : W.p=P := (R.makes.wilson.represents datum.cutoff datum.period i datum.below.le).vac
  have hxK : X.activities.KBound X.p w := by rw [hx]; exact S.actual_forced
  have hyK : W.activities.KBound W.p w := (R.makes.wilson.represents datum.cutoff datum.period i datum.below.le).good.labels.boundK
  have ht : ‖t‖=‖X.activities.gas X.p U‖*Real.exp (-W.exponent U) := by
    simp only [t,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hpay : SumBudget (fun j => X.p.mass (X.activities.forced j).support ‖t*row j‖) cap := by
    by_cases hc : flags P.threshold U = ∅
    · have hx0 : flags X.p.threshold U = ∅ := by rwa [hx]
      have hy0 : flags W.p.threshold U = ∅ := by rwa [hy]
      have h0 (j : ℕ) : row j=0 := by
        dsimp only [row]
        rw [ActualWilsonSpectatorGerm.dressed_clean X j U hx0,ActualWilsonSpectatorGerm.dressed_clean W (e j) U hy0]
        ring
      have hz : 0 ≤ cap := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (forcedPos C.path.levels i).le)
        (Real.exp_pos _).le) hf
      simpa only [h0,mul_zero,norm_zero,BudgetPoint.mass,zero_mul,mul_zero] using
        (show SumBudget (fun _ : ℕ => (0:ℝ)) cap from ⟨fun _ => le_rfl,summable_zero,tsum_zero.le.trans hz⟩)
    have hX : ‖X.activities.gas X.p U‖ ≤ w*vcap := by
      apply (vacuum X hw hxK U).trans_eq
      rw [hx,if_neg hc]
    have hW : ‖W.activities.gas W.p U‖ ≤ w*vcap := by
      apply (vacuum W hw hyK U).trans_eq
      rw [hy,if_neg hc]
    have hsc : ‖t‖*b=‖W.activities.gas W.p U‖+‖X.activities.gas X.p U‖ := by
      rw [ht]
      exact ActualWilsonSpectatorNumerator.scalar X W U (congrFun (S.output.output_vacuum R.makes datum.below hFine) U)
    have he : (fun j => X.p.mass (X.activities.forced j).support ‖t*row j‖) =
        fun j => ‖t‖*X.p.mass (X.activities.forced j).support ‖row j‖ := by
      funext j
      simp only [BudgetPoint.mass,norm_mul]
      ring
    rw [he]
    have p := budget_scale (norm_nonneg t) hs
    refine ⟨p.1,p.2.1,p.2.2.trans ?_⟩
    rw [←mul_assoc,hsc]
    exact mul_le_mul_of_nonneg_right (show ‖W.activities.gas W.p U‖+‖X.activities.gas X.p U‖ ≤ 2*w*vcap by
      linarith only [hW,hX]) hf
  refine ⟨hpay,?_⟩
  have hp := budget_mono hpay (fun j => norm_nonneg (t*row j))
    (fun j => X.p.loMass (X.activities.forced j).support _ (norm_nonneg _))
  change ‖t*(∑' j, row j)‖ ≤ cap
  rw [←tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hp.2.1).trans hp.2.2

end YM.Integration.ActualWilsonRootedNumerator
