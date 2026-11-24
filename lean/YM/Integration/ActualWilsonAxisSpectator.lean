import YM.Integration.ActualWilsonSingletonReentry
import YM.Integration.ActualWilsonSpectatorDifference

/-! Pointwise one-mark error and its original Wilson graph coordinate. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualWilsonAxisSpectator

open Function Set Lattice Wilson RG Marker Source Labels RG3.Script.Picnic RG3.Forms
open Comparison.RG02 LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Extra.Histories Relay Bid Trace.Physical Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato RG16 RG16.Guarding
open SelectedCofactorCancellation ActualSelectedCoveredCofactor ActualSelectedModelIntegral
open ActualWilsonGraphReclosure ActualWilsonForcedSlots ActualWilsonSpectatorDifference
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {d : ℕ} {E : Frame G d}

theorem pure_entry (q : Coefficient E n) (hx : q.x = 0) (hr : q.regular = 0)
    (o : Site n) (T : SectionData E) (X : Rep G n) (U : Config G n) :
    q.exponentialEntry o T X U = 0 := by
  have hm (i : ℕ) : q.maskedTerm X i U = 0 := by
    simp [Coefficient.maskedTerm,hr,masked]
  simp [Coefficient.exponentialEntry,hx,hm,SectionData.places,SectionData.evaluate,masked]

variable (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
    {M : AnalyticOutput caps Y K F} {delta : ℝ} {forcedOrder : ℕ}

def ordinary (S : Chosen K I M) (x : IndependentTests J.tests) (v : V)
    (U : Config G (R.family.side datum.level datum.period)) : ℂ :=
  ((R.family.path.rep datum.cutoff datum.period datum.level).eval U : ℂ) *
    ((S.output.residual.leaf (testInclusion J.tests x)).log U).part (B.fire v)

def spectator (S : Chosen K I M) (x : IndependentTests J.tests) (v : V)
    (U : Config G (R.family.side datum.level datum.period)) : ℂ :=
  let X := S.output.carrier.rep
  let W := R.family.path.rep datum.cutoff datum.period datum.level
  let e := address X (OriginalForcedAddresses.actual_keeper R hG
    datum.cutoff datum.level datum.period datum.below.le)
  ∑' j, ((S.output.residual.leaf (testInclusion J.tests x)).contents.each j U).part (B.fire v) *
    ((Real.exp (X.exponent U) : ℂ) * dressed X j U -
      (Real.exp (W.exponent U) : ℂ) * dressed W (e j) U)

def axisError (S : Chosen K I M) (x : IndependentTests J.tests) (v : V)
    (U : Config G (R.family.side datum.level datum.period)) : ℂ :=
  ((S.output.output.leaf (testInclusion J.tests x)).density U).part (B.fire v) -
    ((S.output.formalAligned.leaf (testInclusion J.tests x)).density U).part (B.fire v)

/-- The exact local error on this picked source axis is the ordinary
log, an original priced zero-germ insertion, and the signed change of its
spectator minor. -/
theorem fields (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (hLate : ActualSelectedCofactorFunding.start R.family hG R.makes (Fintype.card V) ≤ datum.level)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (hFine : I.carrier.rep.eval =
      (R.family.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (x : IndependentTests J.tests) (v : V) (ho : F.coarseRoots v = 0)
    (hp : R.family.ref (J.outputWeight v) ≤ datum.level) :
    let C := R.family
    let N := datum.cutoff
    let p := datum.period
    let i := datum.level
    let d := J.outputWeight v
    let g := Pert.Asymptotics.regulatorRun C N p (i+1)
    let r := F.kernelCosts v * g^forcedOrder / F.outputRadii v
    ∃ b : store C d p i, reads d N p i b r ∧ b.x = 0 ∧ page d p i b = 0 ∧
      axisError R S x v = ordinary R S x v + value d N p i b + spectator R hG S x v := by
  intro C N p i d g r
  let D := S.output.residual.leaf (testInclusion J.tests x)
  let X := S.output.carrier
  let W := C.path.rep N p i
  let t := testInclusion J.tests x
  have hvac := S.output.output_vacuum R.makes datum.below hFine
  obtain ⟨q,hx,hr,hq,hfmt,hprice,hbook,hx',hr',_,_,_⟩ :=
    ActualWilsonSingletonReentry.selected R hG S H v hreserve ho hFine x
  let b := original R hG datum.below.le X q
  have hvalue : value d N p i b = gas W b := by
    funext U
    change (W.eval U : ℂ) * b.exponentialEntry 0 (C.localSection d) W U + _ = _
    rw [pure_entry b hx' hr',mul_zero,zero_add]
    rfl
  have hz := (ActualWilsonForcedGraph.gas_coordinate R.makes datum.below.le hp W b b hbook hvalue).1
  refine ⟨b,hbook,hx',hz,?_⟩
  funext U
  have hmodel : (S.output.formalAligned.leaf t).density U = W.eval U • S.output.modelValue t U := by
    rw [S.output.formal_full,hvac]
    rfl
  have hn := (ActualSelectedModelIntegral.weighted_defect R.makes S t U).symm.trans
    (ActualSelectedCofactorFunding.weighted_identity hG R.makes S hLate hFine H x U)
  have ha : axisError R S x v U = (numerator S t U).part (B.fire v) := by
    have hfull : (S.output.output.leaf t).density U - W.eval U • S.output.modelValue t U =
        numerator S t U := hn
    rw [← hmodel] at hfull
    have hh := congrArg (fun y : Poly B => y.part (B.fire v)) hfull
    change ((S.output.output.leaf t).density U).part (B.fire v) -
      ((S.output.formalAligned.leaf t).density U).part (B.fire v) = _
    simpa only [Extra.Trajectories.part_sub] using hh
  have hg : gas X.rep q U = (Real.exp (X.rep.exponent U) : ℂ) * singletonRows D U v := by
    unfold gas
    rw [(rows S.actual_forced q (rem_dominated hprice) U).2]
    congr 1
    unfold singletonRows
    exact tsum_congr (fun j => by rw [hq]; simp only [dressed, coat_pinned,D])
  have hnull := (paired R hG datum.below.le X hvac S.actual_forced q hfmt hprice U).2
  have hsplit : gas X.rep q U - value d N p i b U = spectator R hG S x v U := by
    change (X.rep.eval U : ℂ) * q.exponentialEntry 0 (C.localSection d) X.rep U + _ - _ = _
      at hnull
    rw [pure_entry q hx hr,mul_zero,zero_add] at hnull
    simpa only [gas,spectator,hq] using hnull
  have hnum : (numerator S t U).part (B.fire v) = W.eval U • (D.log U).part (B.fire v) +
      Real.exp (X.rep.exponent U) • singletonRows D U v :=
    numerator_singleton hG R.makes S hLate H x U v
  change axisError R S x v U = ordinary R S x v U + value d N p i b U + spectator R hG S x v U
  rw [ha]
  calc
    (numerator S t U).part (B.fire v) = ordinary R S x v U + gas X.rep q U := by
      rw [hg]
      change _ = (W.eval U : ℂ) * (D.log U).part (B.fire v) + _
      simpa only [Complex.real_smul] using hnum
    _ = _ := by linear_combination hsplit

/-- On the fixed regulator the axis has the original graph realization as
soon as its ordinary field and the actual paired spectator difference are
paid. Its engineering factor is the original level factor. -/
theorem engineering (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (hLate : ActualSelectedCofactorFunding.start R.family hG R.makes (Fintype.card V) ≤ datum.level)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (hFine : I.carrier.rep.eval =
      (R.family.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (x : IndependentTests J.tests) (v : V) (ho : F.coarseRoots v = 0)
    (hp : R.family.ref (J.outputWeight v) ≤ datum.level) :
    let C := R.family
    let N := datum.cutoff
    let p := datum.period
    let i := datum.level
    let d := J.outputWeight v
    let g := Pert.Asymptotics.regulatorRun C N p (i+1)
    let r := F.kernelCosts v * g^forcedOrder / F.outputRadii v
    let z := ((C.S.block i).val : ℂ)^d
    ∀ (u : C.label d) (a c : ℝ), Ink C N p d i (ordinary R S x v) u a →
      Nullity C N p d i (spectator R hG S x v) c →
      Ink C N p d i (z • axisError R S x v) (z • u) (‖z‖ * (a+r+c)) := by
  intro C N p i d g r z u a c ha hc
  obtain ⟨b,hb,_,hz,he⟩ := fields R hG S H hLate hreserve hFine x v ho hp
  have hb' : Nullity C N p d i (value d N p i b) r := ⟨b,hb,hz,rfl⟩
  have h := ((ha.combine hb' R.makes hp datum.below.le).combine hc R.makes hp datum.below.le)
  have haxis : Ink C N p d i (axisError R S x v) u (a+r+c) := by
    rw [he]
    simpa only [add_zero] using h
  exact haxis.scale z R.makes hp datum.below.le

end YM.Integration.ActualWilsonAxisSpectator
