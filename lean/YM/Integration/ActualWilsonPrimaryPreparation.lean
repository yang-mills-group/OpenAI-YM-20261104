import YM.Integration.ActualWilsonAxisSpectator
import YM.RG3.Press.Sitting
import YM.RG3.Primary.Emboss

/-! Physical primary extraction on the original Wilson family and its chosen
local output uses one stencil, budget point and period. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualWilsonPrimaryPreparation
open Function Set Finset Lattice Wilson RG Marker Source Labels
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 Trace.Physical Trace.Physical.GermGraph
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {G : Gauge}

/-- The original family placement receipt bounds the entire degree stencil. -/
theorem stencil (R : Run G) (d i p : ℕ) (hi : R.family.ref d ≤ i) :
    minSide G d ≤ (R.family.side i p).val := by
  unfold minSide
  apply Finset.sup_le
  intro x hx
  apply Finset.sup_le
  intro a _
  exact R.makes.places d i p hi x hx a

/-- Readability on every original regulator above this degree's reference. -/
theorem original (R : Run G) (d N p i : ℕ) (hi : R.family.ref d ≤ i) (hN : i ≤ N) :
    let C := R.family
    let W := C.path.rep N p i
    Push.Local.Readable C.params (C.localSection d) W.p (C.side i p)
      (price G (max W.p.order W.p.power)) := by
  have hz : (R.family.path.rep N p i).p = R.family.path.levels.budget i :=
    (R.makes.wilson.represents N p i hN).vac
  have hi' := (R.makes.stages d).2 i hi
  apply Push.Local.foundation_readable G d (stencil R d i p hi)
  · rw [hz]
    exact (Nat.le_succ d).trans hi'.1
  · rw [hz]
    exact hi'.2

/-- All forced shapes are accessible on this exact run and every stored level. -/
theorem accessible (R : Run G) (hG : G.Simple) (N p i : ℕ) (hN : i ≤ N) :
    RG3.Press.Accessible (R.family.path.rep N p i) :=
  RG3.Press.access_folio _ rfl (R.tuning.receipts.samples hG N i p hN).forced

/-- The two representatives involved in the signed comparison use the same
native target budget point and physical readability receipt. -/
theorem selected (R : Run G) (d : ℕ)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
    {M : AnalyticOutput caps Y K F}
    (S : Chosen K I M)
    (hi : R.family.ref d ≤ datum.level) :
    let C := R.family
    let X := S.output.carrier.rep
    Push.Local.Readable C.params (C.localSection d) X.p (C.side datum.level datum.period)
      (price G (max X.p.order X.p.power)) := by
  let W := R.family.path.rep datum.cutoff datum.period datum.level
  have hz : S.output.carrier.rep.p = W.p := S.output.carrier.point.trans
    (R.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le).vac.symm
  change Push.Local.Readable _ _ S.output.carrier.rep.p _ _
  rw [hz]
  exact original R d datum.cutoff datum.period datum.level hi datum.below.le

end YM.Integration.ActualWilsonPrimaryPreparation
