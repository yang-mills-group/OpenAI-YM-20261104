import YM.Integration.WilsonMeasuredCourseSourceGerm
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Move

/-! The same original held source has one measured germ at its own address,
including the scalar. The measured and Wilson activity values may differ. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkGerm
open Function Filter Lattice Wilson RG RG.Shoot Marker Overlay Source Labels
open Extra.Histories Relay PhysicalNext Repeat Legato Graces Roost
open Pressure Testing Input Precision Org Supply Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe
open AllOrder AllOrder.Transit WheelP AllOrder.Floe QuadraticLocal.Advent
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph RG16.Guarding
open ProjectorNext.Equivariance
open scoped Topology Classical

private theorem hosted {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d}
    (A:Hol G) (o:Site n) (q:Coefficient F n) (P W:Rep G n)
    (point:P.p=W.p) (slots:P.activities.forced=W.activities.forced)
    (layout:q.Format o A W) {κ r:ℝ} (price:q.remBound o W κ r) :
    q.Format o A P ∧ q.remBound o P κ r := by
  refine ⟨⟨?_,layout.origin,layout.identity_null,layout.projects,?_,?_,layout.invariant,?_,
    layout.borel⟩,?_⟩
  · simpa only [point] using layout.smooth
  · simpa only [point,slots] using layout.forcing
  · simpa only [slots] using layout.carried
  · simpa only [point,slots] using layout.supported
  · simpa only [Coefficient.remBound,point,slots] using price

variable {G:Gauge} (R:Run G)
theorem actual {i m N per k d:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀ j,Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (entered:m ≤ i) (live:i ≤ N) (horizon:R.family.ref d ≤ i) (o:Site (R.family.side i per))
    (q r:store R.family d per i) {κ η a b:ℝ}
    (model:q.Format o R.family.params (Ψ i)) (price:q.remBound o (Ψ i) κ a)
    (physical:r.Format o R.family.params (R.family.path.rep N per i))
    (billed:r.remBound o (R.family.path.rep N per i) η b)
    (agreed:q.density o (R.family.localSection d) (Ψ i) =ᶠ[𝓝 1]
      r.density o (R.family.localSection d) (R.family.path.rep N per i)) :
    projection (R.family.labels.level d) R.family.params (Ψ i).p.threshold o q =
    projection (R.family.labels.level d) R.family.params (R.family.path.rep N per i).p.threshold o r := by
  let C:=R.family
  let P:=C.path.rep N per i
  obtain ⟨point,slots,_⟩:=WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course entered live
  change P.p=(Ψ i).p at point
  change P.activities.forced=(Ψ i).activities.forced at slots
  have common:(Ψ i).eval=P.eval:=(later R π Γ Ψ course entered live).view
  obtain ⟨form,fee⟩:=hosted C.params o q P (Ψ i) point slots model price
  have view:q.density o (C.localSection d) P =ᶠ[𝓝 1] q.density o (C.localSection d) (Ψ i):=by
    filter_upwards [Juniper.Caret.flat_flags (C.side i per) P.p.threshold P.p.threshold_pos] with U clean
    change flags P.p.threshold U=∅ at clean
    have fresh:flags (Ψ i).p.threshold U=∅:=by simpa only [←point] using clean
    change (P.eval U:ℂ)*q.exponentialEntry o (C.localSection d) P U+ActualWilsonGraphReclosure.gas P q U=
      ((Ψ i).eval U:ℂ)*q.exponentialEntry o (C.localSection d) (Ψ i) U+ActualWilsonGraphReclosure.gas (Ψ i) q U
    rw [ActualWilsonGraphReclosure.gas_unflagged P q U clean,
      ActualWilsonGraphReclosure.gas_unflagged (Ψ i) q U fresh,common]
    simp only [Coefficient.exponentialEntry,Coefficient.maskedTerm,point]
  rw [←point]
  exact intrinsic_at (C.labels.level d) C.params (C.localSection d) (R.makes.sections d) o
    (R.makes.places d i per horizon) (dimensions d N per i R.makes horizon live).1
    (dimensions d N per i R.makes horizon live).2 (sections_visit R.makes horizon o)
    q r form physical ⟨κ,a,fee⟩ ⟨η,b,billed⟩ (view.trans agreed)

end YM.Integration.WilsonThermometerSameWalkGerm
end
