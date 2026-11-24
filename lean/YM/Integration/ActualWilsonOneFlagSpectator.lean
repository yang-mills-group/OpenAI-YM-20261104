import YM.Integration.ActualWilsonFlagCofactor
import YM.Integration.ActualWilsonSpectatorGerm

/-! The whole original signed physical spectator on the one-flag sector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonOneFlagSpectator
open Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Extra.Histories Trace.Physical Trace.Physical.GermGraph
open ActualWilsonAxisSpectator ActualWilsonPacketSplit
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}

theorem selected (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    (S : Chosen K I M) (x : IndependentTests J.tests) (v : V)
    (U : Config G (R.family.side datum.level datum.period))
    (hcard : (flags (R.family.path.levels.budget datum.level).threshold U).card ≤ 1) :
    let C := R.family
    let W := C.path.rep datum.cutoff datum.period datum.level
    let X := S.output.carrier.rep
    let D := S.output.residual.leaf (testInclusion J.tests x)
    let Fg := flags (C.path.levels.budget datum.level).threshold U
    spectator R hG S x v U = (∑' j, if inventory X j=Fg then (D.contents.each j U).part (B.fire v) else 0) *
      ((Real.exp (X.exponent U) : ℂ)-(Real.exp (W.exponent U) : ℂ)) := by
  intro C W X D Fg
  let k := OriginalForcedAddresses.actual_keeper R hG datum.cutoff datum.level datum.period datum.below.le
  let e := ActualWilsonForcedSlots.address X k
  have hx : flags X.p.threshold U=Fg := congrArg (fun p : BudgetPoint => flags p.threshold U) S.output.carrier.point
  have hw : flags W.p.threshold U=Fg := congrArg (fun p : BudgetPoint => flags p.threshold U)
    (R.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le).vac
  have hxc : (flags X.p.threshold U).card ≤ 1 := by rw [hx]; exact hcard
  have hwc : (flags W.p.threshold U).card ≤ 1 := by rw [hw]; exact hcard
  let a := (Real.exp (X.exponent U) : ℂ)
  let b := (Real.exp (W.exponent U) : ℂ)
  let row j := (D.contents.each j U).part (B.fire v)
  change (∑' j, row j * (a*dressed X j U-b*dressed W (e j) U)) =
    (∑' j, if inventory X j=Fg then row j else 0) * (a-b)
  rw [←tsum_mul_right]
  apply tsum_congr
  intro j
  have hb : inventory W (e j)=inventory X j := (ActualWilsonForcedSlots.barcode (X := X) k j).2
  rw [ActualWilsonFlagCofactor.one_flag X j U hxc,ActualWilsonFlagCofactor.one_flag W (e j) U hwc,hx,hw,hb]
  by_cases h : inventory X j=Fg <;> simp [h]

end YM.Integration.ActualWilsonOneFlagSpectator
