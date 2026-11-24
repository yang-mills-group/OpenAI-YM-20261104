import YM.Integration.WilsonPhysicalAllGradeWeakElection
import YM.Integration.WilsonPhysicalWeakSameStation
import YM.Integration.WilsonPositionCapTransport

/-! One group of original physical station fields on the elected field chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakRegisteredGroup
open Function Filter Spec Table Climb PhysMS PhysMS.Frame Trace.Pilot Trace.Target
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open WilsonPhysicalWeakWallStaff WilsonPhysicalWeakWallBounded WilsonPhysicalWeakSameStation
open WilsonPositionThermometerCapStation WilsonPositionCapTransport Next.UVStress
open scoped Classical Topology
open PhysicalNext.Repeat.Legato
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}(simple:G.Simple)
  (assignment:Assignment F J H l simple)

theorem original (axes:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)(D:ℕ):
    ∃A:ℝ→Group R.family D,
      (∀r,∀cap:D≤(assignment.day r).1,A r=(trim cap (assignment.day r).2).room) ∧
      Book (f:=f) (l:=l) (H:=H) A (provisional assignment.day) ∧
      Book (f:=f) (l:=l) (H:=H) (through (provisional assignment.day) J A) J := by
  classical
  obtain ⟨r₀,cap₀⟩:=(assignment.rises.eventually_ge_atTop D).exists
  let A (r:ℝ):Group R.family D:=if cap:D≤(assignment.day r).1 then (trim cap (assignment.day r).2).room
    else (trim cap₀ (assignment.day r₀).2).room
  have same(r:ℝ)(cap:D≤(assignment.day r).1):A r=(trim cap (assignment.day r).2).room:=dif_pos cap
  have booked:Book (f:=f) (l:=l) (H:=H) A (provisional assignment.day):=by
    intro m
    filter_upwards [assignment.sale,assignment.rises.eventually_ge_atTop D,assignment.rises.eventually_ge_atTop m]
      with r sold cap live
    rw [same r cap]
    exact ((admitted F cap live simple (assignment.day r).2 sold).2.2 m le_rfl).2
  have staff:=attended simple F H assignment.day assignment.rises assignment.sale
  have obedient(d:ℕ):∀ᶠr in trail, Frame.obedient F H (provisional assignment.day r) d:=
    (staff d).mono fun _ h=>h.spins (Fin.last d)
  exact ⟨A,same,booked,transported F simple _ J A booked assignment.change obedient axes⟩

end YM.Integration.WilsonPhysicalWeakRegisteredGroup
