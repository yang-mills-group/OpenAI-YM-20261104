import YM.Integration.ActualWilsonSingleFlagGas

/-! Rowwise compensated spectator on the same two genuine Wilson vacua. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonCrossedSpectator
open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Extra.Histories Trace.Physical Trace.Physical.GermGraph
open ActualWilsonAxisSpectator ActualWilsonPacketSplit
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

theorem row (X W : Rep G n) (U : Config G n) (h : X.eval U = W.eval U) (r d e : ℂ) :
    ((X.activities.gas X.p U:ℂ)*(Real.exp (-W.exponent U):ℂ))*
      (r*((Real.exp (X.exponent U):ℂ)*d-(Real.exp (W.exponent U):ℂ)*e)) =
    r*((W.activities.gas W.p U:ℂ)*d-(X.activities.gas X.p U:ℂ)*e) := by
  let a := (Real.exp (X.exponent U):ℂ)
  let b := (Real.exp (W.exponent U):ℂ)
  let c := (Real.exp (-W.exponent U):ℂ)
  let x := (X.activities.gas X.p U:ℂ)
  let y := (W.activities.gas W.p U:ℂ)
  have hxy : a*x=b*y := by
    change Real.exp (X.exponent U)*X.activities.gas X.p U =
      Real.exp (W.exponent U)*W.activities.gas W.p U at h
    simpa only [a,x,b,y,Complex.ofReal_mul] using congrArg Complex.ofReal h
  have hc : c*b=1 := by
    have hh : Real.exp (-W.exponent U)*Real.exp (W.exponent U)=1 := by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
    simpa only [c,b,Complex.ofReal_mul,Complex.ofReal_one] using congrArg Complex.ofReal hh
  change (x*c)*(r*(a*d-b*e))=r*(y*d-x*e)
  calc
    _ = r*((c*(a*x))*d-(c*b)*x*e) := by ring
    _ = r*((c*(b*y))*d-(c*b)*x*e) := by rw [hxy]
    _ = _ := by rw [←mul_assoc c b y,hc,one_mul,one_mul]

theorem filled (X W : Rep G n) (U : Config G n) (h : X.eval U = W.eval U) (i j : ℕ) (r : ℂ)
    (hi : inventory X i = flags X.p.threshold U) (hj : inventory W j = flags W.p.threshold U) :
    ((X.activities.gas X.p U:ℂ)*(Real.exp (-W.exponent U):ℂ))*
      (r*((Real.exp (X.exponent U):ℂ)*dressed X i U-(Real.exp (W.exponent U):ℂ)*dressed W j U)) =
    r*((W.activities.gas W.p U:ℂ)-(X.activities.gas X.p U:ℂ)) := by
  rw [row X W U h,ActualWilsonFlagCofactor.filled X i U hi,ActualWilsonFlagCofactor.filled W j U hj,mul_one,mul_one]

theorem selected (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    (S : Chosen K I M)
    (hFine : I.carrier.rep.eval=(R.family.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (x : IndependentTests J.tests) (v : V) (U : Config G (R.family.side datum.level datum.period)) :
    let i := datum.level
    let X := S.output.carrier.rep
    let W := R.family.path.rep datum.cutoff datum.period i
    let D := S.output.residual.leaf (testInclusion J.tests x)
    let e := ActualWilsonForcedSlots.address X (OriginalForcedAddresses.actual_keeper R hG
      datum.cutoff i datum.period datum.below.le)
    let y j := (D.contents.each j U).part (B.fire v)
    ((X.activities.gas X.p U:ℂ)*(Real.exp (-W.exponent U):ℂ))*spectator R hG S x v U =
      ∑' j, y j*((W.activities.gas W.p U:ℂ)*dressed X j U-(X.activities.gas X.p U:ℂ)*dressed W (e j) U) := by
  intro i X W D e y
  change _*(∑' j,y j*((Real.exp (X.exponent U):ℂ)*dressed X j U-
    (Real.exp (W.exponent U):ℂ)*dressed W (e j) U))=_
  rw [←tsum_mul_left]
  apply tsum_congr
  intro j
  exact row X W U (congrFun (S.output.output_vacuum R.makes datum.below hFine) U) (y j) _ _

end YM.Integration.ActualWilsonCrossedSpectator
