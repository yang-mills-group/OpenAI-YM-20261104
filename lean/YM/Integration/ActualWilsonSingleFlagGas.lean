import YM.Integration.ActualWilsonOneFlagSpectator

/-! On a single genuine flag the signed vacuum is a singleton activity
sum, and the entire weighted physical spectator is an original activity difference. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonSingleFlagGas
open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Extra.Histories Trace.Physical Trace.Physical.GermGraph
open ActualWilsonAxisSpectator ActualWilsonPacketSplit ActualWilsonJoinedCofactor
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

theorem admissible_card (W : Rep G n) {U : Config G n} {s : Finset ℕ}
    (h : W.activities.admissible W.p U s) : s.card ≤ (flags W.p.threshold U).card := by
  have p : permits W ∅ ∅ s U := ⟨h.1,fun _ _ => Finset.disjoint_empty_left _,by simpa using h.2⟩
  simpa using ActualWilsonFlagCofactor.flag_count W (Finset.empty_subset _) p

theorem single (W : Rep G n) (U : Config G n) (h : (flags W.p.threshold U).card=1) :
    W.activities.gas W.p U = ∑' j, if inventory W j=flags W.p.threshold U then W.activities.K j U else 0 := by
  let v (s : Finset ℕ) := W.activities.gasOccurrence W.p s U
  let e (j : ℕ) : Finset ℕ := {j}
  have hin : Injective e := by
    intro j k h
    exact Finset.singleton_injective h
  have hs : Function.support v ⊆ range e := by
    intro s hn
    have hp : W.activities.admissible W.p U s := by
      by_contra hp
      exact hn (if_neg hp)
    have hc := admissible_card W hp
    have hpos : 0 < s.card := by
      by_contra! hzero
      have hS := card_eq_zero.mp (by omega : s.card=0)
      have he : flags W.p.threshold U = ∅ := by simpa [hS] using hp.2.symm
      simp [he] at h
    obtain ⟨j,hj⟩ := Finset.card_eq_one.mp (by omega : s.card=1)
    exact ⟨j,hj.symm⟩
  change (∑' s, v s)=_
  rw [←hin.tsum_eq hs]
  apply tsum_congr
  intro j
  simp [v,e,Activities.gasOccurrence,Activities.admissible,inventory]

theorem cancel (X W : Rep G n) (U : Config G n) (h : X.eval U = W.eval U) (r : ℂ) :
    (X.activities.gas X.p U : ℂ)*(Real.exp (-W.exponent U) : ℂ)*
      (r*((Real.exp (X.exponent U) : ℂ)-(Real.exp (W.exponent U) : ℂ))) =
    ((W.activities.gas W.p U-X.activities.gas X.p U : ℝ) : ℂ)*r := by
  let a := (Real.exp (X.exponent U) : ℂ)
  let b := (Real.exp (W.exponent U) : ℂ)
  let c := (Real.exp (-W.exponent U) : ℂ)
  let x := (X.activities.gas X.p U : ℂ)
  let y := (W.activities.gas W.p U : ℂ)
  have he : a*x=b*y := by
    change Real.exp (X.exponent U)*X.activities.gas X.p U =
      Real.exp (W.exponent U)*W.activities.gas W.p U at h
    simpa only [a,x,b,y,Complex.ofReal_mul] using congrArg Complex.ofReal h
  have hc : c*b=1 := by
    have hh : Real.exp (-W.exponent U)*Real.exp (W.exponent U)=1 := by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
    simpa only [c,b,Complex.ofReal_mul,Complex.ofReal_one] using congrArg Complex.ofReal hh
  rw [Complex.ofReal_sub]
  change x*c*(r*(a-b))=(y-x)*r
  calc
    _ = (c*(a*x)-(c*b)*x)*r := by ring
    _ = (c*(b*y)-(c*b)*x)*r := by rw [he]
    _ = _ := by rw [←mul_assoc c b y,hc,one_mul,one_mul]

theorem selected (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    (S : Chosen K I M)
    (hFine : I.carrier.rep.eval=(R.family.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (x : IndependentTests J.tests) (v : V) (U : Config G (R.family.side datum.level datum.period))
    (h : (flags (R.family.path.levels.budget datum.level).threshold U).card=1) :
    let Fg := flags (R.family.path.levels.budget datum.level).threshold U
    let W := R.family.path.rep datum.cutoff datum.period datum.level
    let X := S.output.carrier.rep
    let D := S.output.residual.leaf (testInclusion J.tests x)
    let vacuum (P : Rep G (R.family.side datum.level datum.period)) :=
      ∑' j, if inventory P j=Fg then P.activities.K j U else 0
    let rows := ∑' j, if inventory X j=Fg then (D.contents.each j U).part (B.fire v) else 0
    (X.activities.gas X.p U : ℂ)*(Real.exp (-W.exponent U) : ℂ)*spectator R hG S x v U =
      ((vacuum W-vacuum X : ℝ) : ℂ)*rows := by
  intro Fg W X D vacuum rows
  have hx : flags X.p.threshold U=Fg := congrArg (fun p : BudgetPoint => flags p.threshold U) S.output.carrier.point
  have hw : flags W.p.threshold U=Fg := congrArg (fun p : BudgetPoint => flags p.threshold U)
    (R.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le).vac
  have hX : X.activities.gas X.p U=vacuum X := by rw [single X U (hx ▸ h),hx]
  have hW : W.activities.gas W.p U=vacuum W := by rw [single W U (hw ▸ h),hw]
  have hs : spectator R hG S x v U=rows*((Real.exp (X.exponent U) : ℂ)-(Real.exp (W.exponent U) : ℂ)) :=
    ActualWilsonOneFlagSpectator.selected R hG S x v U h.le
  rw [hs,cancel X W U (congrFun (S.output.output_vacuum R.makes datum.below hFine) U),hX,hW]

end YM.Integration.ActualWilsonSingleFlagGas
