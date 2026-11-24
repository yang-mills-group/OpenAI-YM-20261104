import YM.Integration.ActualWilsonFailedMaskPrice
import YM.Integration.ActualWilsonSpectatorGerm

/-! A regulator-uniform signed numerator estimate using the two genuine
Wilson vacuum factors and their actual scalar-field equality. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonSpectatorNumerator
open Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Extra.Histories Trace.Physical Trace.Physical.GermGraph
open ActualWilsonAxisSpectator
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

theorem scalar (X W : Rep G n) (U : Config G n) (h : X.eval U = W.eval U) :
    (‖X.activities.gas X.p U‖ * Real.exp (-W.exponent U)) *
      (Real.exp (X.exponent U)+Real.exp (W.exponent U)) =
      ‖W.activities.gas W.p U‖+‖X.activities.gas X.p U‖ := by
  let a := Real.exp (X.exponent U)
  let b := Real.exp (W.exponent U)
  let c := Real.exp (-W.exponent U)
  let x := X.activities.gas X.p U
  let y := W.activities.gas W.p U
  have he : |a*x|=|b*y| := congrArg abs h
  rw [abs_mul,abs_mul,abs_of_pos (show 0<a from Real.exp_pos _),abs_of_pos (show 0<b from Real.exp_pos _)] at he
  have hc : c*b=1 := by
    change Real.exp _*Real.exp _=1
    rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
  change ((abs x)*c)*(a+b)=(abs y)+(abs x)
  calc
    _ = c*(a*(abs x))+(abs x)*(c*b) := by ring
    _ = c*(b*(abs y))+(abs x)*(c*b) := by rw [he]
    _ = _ := by rw [←mul_assoc,hc,one_mul,mul_one]

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
    let W := C.path.rep datum.cutoff datum.period i
    let X := S.output.carrier.rep
    let w := C.path.levels.clock.forcedAllowance i
    let g := Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (i+1)
    let fee := forcedDivisor C i*(F.kernelCosts v*g^a/F.outputRadii v)
    ‖(X.activities.gas X.p U : ℂ)*(Real.exp (-W.exponent U) : ℂ)*spectator R hG S x v U‖ ≤ 2*w*fee := by
  intro C i W X w g fee
  have hp := (ActualWilsonSpectatorBudget.selected R hG S H hLate hres x v U).2
  change ‖spectator R hG S x v U‖ ≤ (Real.exp (X.exponent U)+Real.exp (W.exponent U))*fee at hp
  have hf : 0 ≤ fee := by
    by_contra! h
    exact (not_lt_of_ge ((norm_nonneg _).trans hp)) (mul_neg_of_pos_of_neg (add_pos (Real.exp_pos _) (Real.exp_pos _)) h)
  have hw : w ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
  have hW := (R.makes.wilson.represents datum.cutoff datum.period i datum.below.le).good.labels.boundK
  have ht : W.p=C.path.levels.budget i := (R.makes.wilson.represents datum.cutoff datum.period i datum.below.le).vac
  by_cases hc : flags (C.path.levels.budget i).threshold U=∅
  · rw [ActualWilsonSpectatorGerm.clean R hG S U hc x v,mul_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (forcedPos C.path.levels i).le) hf
  have hx : flags X.p.threshold U ≠ ∅ := by
    change flags S.output.carrier.rep.p.threshold U ≠ ∅
    rwa [S.output.carrier.point]
  have hy : flags W.p.threshold U ≠ ∅ := by rwa [ht]
  have hx0 := ActualWilsonFailedMaskPrice.vacuum S.actual_forced hw U
  have hy0 : ‖W.activities.gas W.p U‖ ≤ if flags W.p.threshold U=∅ then 1 else w :=
    ActualWilsonFailedMaskPrice.vacuum (P := W) hW hw U
  rw [if_neg hx] at hx0
  rw [if_neg hy] at hy0
  have hsc := scalar X W U (congrFun (S.output.output_vacuum R.makes datum.below hFine) U)
  calc
    _ = (‖X.activities.gas X.p U‖*Real.exp (-W.exponent U))*‖spectator R hG S x v U‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    _ ≤ (‖X.activities.gas X.p U‖*Real.exp (-W.exponent U)) *
        ((Real.exp (X.exponent U)+Real.exp (W.exponent U))*fee) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    _ = (‖W.activities.gas W.p U‖+‖X.activities.gas X.p U‖)*fee := by rw [←mul_assoc,hsc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hx0,hy0]) hf

end YM.Integration.ActualWilsonSpectatorNumerator
