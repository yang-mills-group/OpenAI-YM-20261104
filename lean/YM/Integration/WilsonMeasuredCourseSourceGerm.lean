import YM.Integration.WilsonMeasuredCourseQuietSlots
import YM.Integration.ActualWilsonGraphReclosure
import YM.Juniper.Caret.Regular

/-! Read a charged source of the measured course in the original Wilson germ.
Its regular and forced budgets transport at their original radius. The two
full group functions agree on the healthy chart. Their difference on a failed
field keeps both signed marked gas sums, with their own spectator weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredCourseSourceGerm
open Function Filter Lattice Wilson RG RG.Shoot Marker Overlay Source Labels
open Extra.Histories Relay PhysicalNext Repeat Legato Graces Roost
open Pressure Testing Input Precision Org Supply Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe
open AllOrder AllOrder.Transit WheelP AllOrder.Floe QuadraticLocal.Advent
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph RG16.Guarding
open scoped Topology Classical
variable {G:Gauge} (R:Run G)

private theorem relocate {n:Side} {d:ℕ} {F:Frame G d}
    (A:Source.Hol G) (o:Site n) (q:Coefficient F n) (X Y:Rep G n)
    (point:X.p=Y.p) (slots:X.activities.forced=Y.activities.forced)
    (layout:q.Format o A Y) (κ r:ℝ) (price:q.remBound o Y κ r) :
    q.Format o A X ∧ q.remBound o X κ r := by
  refine ⟨⟨?_,layout.origin,layout.identity_null,layout.projects,?_,?_,layout.invariant,?_,
    layout.borel⟩,?_⟩
  · simpa only [point] using layout.smooth
  · simpa only [point,slots] using layout.forcing
  · simpa only [slots] using layout.carried
  · simpa only [point,slots] using layout.supported
  · simpa only [Coefficient.remBound,point,slots] using price

theorem original {i m N per k d:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀ j, Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (started:m ≤ i) (live:i ≤ N) (q:store R.family d per i) {r:ℝ}
    (layout:q.Format 0 R.family.params (Ψ i)) (price:q.remBound 0 (Ψ i) (safety R.family i) r) :
    let C:=R.family
    let P:=C.path.rep N per i
    let F:=q.density 0 (C.localSection d) (Ψ i)
    reads (C:=C) d N per i q r ∧
    (∀ U, value (C:=C) d N per i q U - F U =
      ActualWilsonGraphReclosure.gas P q U-ActualWilsonGraphReclosure.gas (Ψ i) q U) ∧
    value (C:=C) d N per i q =ᶠ[𝓝 1] F := by
  intro C P F
  obtain ⟨point,slots,_⟩ := WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course started live
  change P.p=(Ψ i).p at point
  change P.activities.forced=(Ψ i).activities.forced at slots
  obtain ⟨form,charged⟩ := relocate C.params 0 q P (Ψ i) point slots layout (safety C i) r price
  have common : (Ψ i).eval=P.eval := (later R π Γ Ψ course started live).view
  have all (U : Config G (C.side i per)) :
      value (C:=C) d N per i q U-F U =
        ActualWilsonGraphReclosure.gas P q U-ActualWilsonGraphReclosure.gas (Ψ i) q U := by
    change ((P.eval U:ℂ)*q.exponentialEntry 0 (C.localSection d) P U+ActualWilsonGraphReclosure.gas P q U)-
      (((Ψ i).eval U:ℂ)*q.exponentialEntry 0 (C.localSection d) (Ψ i) U+ActualWilsonGraphReclosure.gas (Ψ i) q U)=_
    rw [common]
    simp only [Coefficient.exponentialEntry,Coefficient.maskedTerm,point]
    abel
  refine ⟨⟨form,charged⟩,all,?_⟩
  filter_upwards [Juniper.Caret.flat_flags (C.side i per) P.p.threshold P.p.threshold_pos] with U quiet
  have quiet' : flags (Ψ i).p.threshold U=∅ := by simpa only [←point] using quiet
  have equal:=all U
  rw [ActualWilsonGraphReclosure.gas_unflagged P q U quiet,
    ActualWilsonGraphReclosure.gas_unflagged (Ψ i) q U quiet',sub_self] at equal
  exact sub_eq_zero.mp equal

theorem primary {i m N per k d:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀ j, Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (started:m ≤ i) (live:i ≤ N) (ready:R.family.ref d ≤ i)
    (q:store R.family d per i) {r b:ℝ} (layout:q.Format 0 R.family.params (Ψ i))
    (price:q.remBound 0 (Ψ i) (safety R.family i) r)
    (v:R.family.label d) (f:Config G (R.family.side i per)→ℂ)
    (seen:Ink R.family N per d i f v b)
    (germ:f =ᶠ[𝓝 1] q.density 0 (R.family.localSection d) (Ψ i)) :
    v=page (C:=R.family) d per i q := by
  obtain ⟨receipt,_,common⟩ := original R π Γ Ψ course started live q layout price
  obtain ⟨s,paid,read,represented⟩ := seen
  exact read.symm.trans (same_page R.makes live ready paid receipt
    ((EventuallyEq.of_eq represented.symm).trans (germ.trans common.symm)))

end YM.Integration.WilsonMeasuredCourseSourceGerm
end

