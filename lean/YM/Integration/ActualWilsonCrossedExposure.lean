import YM.Integration.ActualWilsonFlagReadout
import YM.Integration.WilsonSpectatorReadout
import YM.Integration.ActualSelectedModelEnvelope

/-! The true Wilson density against the screened spectator on its actual flagged sector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonCrossedExposure
open MeasureTheory Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Extra.Histories Trace.Physical Trace.Physical.GermGraph
open ActualWilsonAxisSpectator SectorNext.Vacuum Push.AbsoluteSums
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

def bare (X W : Rep G n) (U : Config G n) : ℝ :=
  (Real.exp (X.exponent U)+Real.exp (W.exponent U))*
    ForcedNormalization.flagPrice X.p.threshold (2*flagRate X.p) 1 U

theorem envelope (X W : Rep G n) (hX : Envelope X.exponent) (hW : Envelope W.exponent) :
    Envelope (bare X W) :=
  (hX.exp.add hW.exp).mul (ForcedNormalization.flagPrice_envelope _ _ _)

theorem field (X W : Rep G n) {w fee : ℝ} (hw : 0≤w) (hw1 : w≤1)
    (hW : W.activities.KBound W.p w) (hp : W.p=X.p) (U : Config G n) (f : ℂ)
    (hclean : flags X.p.threshold U=∅ → f=0)
    (hs : ‖f‖≤(Real.exp (X.exponent U-W.exponent U)+1)*
      Real.exp (-flagRate X.p*(flags X.p.threshold U).card)*fee) :
    W.eval U*‖f‖≤w*bare X W U*fee := by
  by_cases hc : flags X.p.threshold U=∅
  · simp [bare,ForcedNormalization.flagPrice,hc,hclean hc]
  let E := Real.exp (-flagRate X.p*(flags X.p.threshold U).card)
  have hv : ‖W.activities.gas W.p U‖≤w*E := by
    apply (ActualWilsonRootedNumerator.vacuum W hw1 hW U).trans_eq
    rw [hp,if_neg hc]
  have hh : W.eval U≤Real.exp (W.exponent U)*(w*E) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hv) (Real.exp_pos _).le
  have ht : Real.exp (W.exponent U)*(Real.exp (X.exponent U-W.exponent U)+1)=
      Real.exp (X.exponent U)+Real.exp (W.exponent U) := by
    rw [mul_add,←Real.exp_add,show W.exponent U+(X.exponent U-W.exponent U)=X.exponent U by ring,mul_one]
  have hE : E*E=Real.exp (-(2*flagRate X.p)*(flags X.p.threshold U).card) := by
    rw [show E*E=Real.exp ((-flagRate X.p*(flags X.p.threshold U).card)+(-flagRate X.p*(flags X.p.threshold U).card)) from (Real.exp_add _ _).symm]
    congr 1
    ring
  calc
    _ ≤ (Real.exp (W.exponent U)*(w*E))*‖f‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ ≤ (Real.exp (W.exponent U)*(w*E))*((Real.exp (X.exponent U-W.exponent U)+1)*E*fee) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (Real.exp_pos _).le (mul_nonneg hw (Real.exp_pos _).le))
    _ = w*(Real.exp (W.exponent U)*(Real.exp (X.exponent U-W.exponent U)+1))*(E*E)*fee := by ring
    _ = _ := by rw [ht,hE,bare,ForcedNormalization.flagPrice,if_neg hc,one_mul];ring

theorem selected (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    {δ : ℝ} {a : ℕ} (S : Chosen K I M) (H : Bounds S δ a)
    (hres : 2*(R.family.path.levels.budget datum.level).supportExponent≤J.outputSupport)
    (x : IndependentTests J.tests) (v : V) (U : Config G (R.family.side datum.level datum.period)) :
    let C := R.family
    let i := datum.level
    let X := S.output.carrier.rep
    let W := C.path.rep datum.cutoff datum.period i
    let w := C.path.levels.clock.forcedAllowance i
    let fee := F.kernelCosts v*(forcedDivisor C i*Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (i+1)^a/F.outputRadii v)
    W.eval U*‖(Real.exp (-W.exponent U):ℂ)*spectator R hG S x v U‖≤w*bare X W U*fee := by
  intro C i X W w fee
  have hW := R.makes.wilson.represents datum.cutoff datum.period i datum.below.le
  have hp : W.p=X.p := hW.vac.trans S.output.carrier.point.symm
  have hw : w≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
  apply field X W (forcedPos C.path.levels i).le hw hW.good.labels.boundK hp U
  · intro hc
    have h1 : (C.path.levels.budget i).supportExponent≤J.outputSupport := by
      linarith only [hres,(C.path.levels.budget i).exponent_pos]
    have hg := WilsonSpectatorReadout.clean R hG S H x v h1 U (by
      simpa only [WilsonSpectatorReadout.dirty,mem_setOf_eq,not_not] using hc)
    rw [hg,mul_zero]
  exact (ActualWilsonFlagReadout.selected R hG S H hres x v U).2.2

end YM.Integration.ActualWilsonCrossedExposure
