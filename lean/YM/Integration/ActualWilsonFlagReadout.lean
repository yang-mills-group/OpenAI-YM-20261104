import YM.Integration.ActualWilsonFlagScreen

/-! The true reweighted signed spectator with the complete exterior and interior flag tariff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonFlagReadout
open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Extra.Histories Trace.Physical Trace.Physical.GermGraph
open ActualWilsonAxisSpectator ActualWilsonPacketSplit SectorNext.Vacuum Push.AbsoluteSums
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

theorem row {c d : ℝ} (y a b : ℂ) :
    (Real.exp (-d):ℂ)*(y*((Real.exp c:ℂ)*a-(Real.exp d:ℂ)*b))=
      y*((Real.exp (c-d):ℂ)*a-b) := by
  have h1 : (Real.exp (-d):ℂ)*(Real.exp c:ℂ)=(Real.exp (c-d):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.exp_add,show -d+c=c-d by ring]
  have h2 : (Real.exp (-d):ℂ)*(Real.exp d:ℂ)=1 := by rw [←Complex.ofReal_mul,←Real.exp_add,neg_add_cancel,Real.exp_zero,Complex.ofReal_one]
  calc
    _ = y*(((Real.exp (-d):ℂ)*(Real.exp c:ℂ))*a-((Real.exp (-d):ℂ)*(Real.exp d:ℂ))*b) := by ring
    _ = _ := by rw [h1,h2,one_mul]

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
    let P := X.p
    let D := S.output.residual.leaf (testInclusion J.tests x)
    let e := ActualWilsonForcedSlots.address X (OriginalForcedAddresses.actual_keeper R hG datum.cutoff i datum.period datum.below.le)
    let t := Real.exp (X.exponent U-W.exponent U)
    let z := Real.exp (-flagRate P*(flags P.threshold U).card)
    let f j := ((D.contents.each j U).part (B.fire v))*((t:ℂ)*dressed X j U-dressed W (e j) U)
    let fee := F.kernelCosts v*(forcedDivisor C i*Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (i+1)^a/F.outputRadii v)
    (Real.exp (-W.exponent U):ℂ)*spectator R hG S x v U=∑' j,f j ∧
      SumBudget (fun j => P.mass (scopes X j) ‖f j‖) ((t+1)*z*fee) ∧
      ‖(Real.exp (-W.exponent U):ℂ)*spectator R hG S x v U‖≤(t+1)*z*fee := by
  intro C i X W P D e t z f fee
  let y j := (D.contents.each j U).part (B.fire v)
  let w := C.path.levels.clock.forcedAllowance i
  let Q := A.outputNorm i
  let keeper := OriginalForcedAddresses.actual_keeper R hG datum.cutoff i datum.period datum.below.le
  have hp : X.p=C.path.levels.budget i := S.output.carrier.point
  have hy : W.p=X.p := (R.makes.wilson.represents datum.cutoff datum.period i datum.below.le).vac.trans hp.symm
  have HX : X.activities.KBound X.p w := by rw [hp]; exact S.actual_forced
  have HW : W.activities.KBound W.p w := (R.makes.wilson.represents datum.cutoff datum.period i datum.below.le).good.labels.boundK
  have hw : w≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
  have hB : Q.B=X.p.B := by rw [hp]; exact (A.output_norm i).block
  have hQ : 2*X.p.supportExponent≤Q.supportExponent := by rw [hp,(A.output_norm i).reserve];exact hres
  obtain ⟨b,hb,hs⟩ := ActualWilsonForcedRow.retained S H v
  have hval (j : ℕ) : ‖y j‖≤b j := (congrArg norm (ActualWilsonForcedRow.each_solution D v j U
    (SelectedCofactorSupportBudget.tagged_summable H.residual_price F.kernel_positive x j U))).le.trans ((hb j).2 x U)
  have HH : SumBudget (fun j => Q.mass (scopes X j) ‖y j‖) fee := budget_mono hs
    (fun j => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (fun j => mul_le_mul_of_nonneg_left (hval j) (Real.exp_pos _).le)
  have HI : SumBudget (fun j => P.mass (scopes X j) ‖f j‖) ((t+1)*z*fee) :=
    ActualWilsonFlagScreen.rows X W Q hw HX HW hy e (fun j => (ActualWilsonForcedSlots.barcode (X := X) keeper j).1) hB hQ U y HH
  have he : (Real.exp (-W.exponent U):ℂ)*spectator R hG S x v U=∑' j,f j := by
    change _*(∑' j,y j*((Real.exp (X.exponent U):ℂ)*dressed X j U-(Real.exp (W.exponent U):ℂ)*dressed W (e j) U))=_
    rw [←tsum_mul_left]
    exact tsum_congr (fun j => row (y j) _ _)
  refine ⟨he,HI,?_⟩
  rw [he]
  have Hf := budget_mono HI (fun j => norm_nonneg (f j)) (fun j => P.loMass _ _ (norm_nonneg _))
  exact (norm_tsum_le_tsum_norm Hf.2.1).trans Hf.2.2

end YM.Integration.ActualWilsonFlagReadout
