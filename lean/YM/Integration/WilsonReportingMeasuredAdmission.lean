import YM.Integration.WilsonReportingMeasuredTender
import YM.Integration.WilsonReportPrescribedTests

/-! Spend the prescribed measured tower's leading measurements and its
actual aligned fields on one fixed layout, prior to every funded source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredAdmission
open Function Filter Finset Set Extraction Table Climb Ward Next.UVStress PhysMS
open RG12 RG17 SharpGram SharpGram.Lenses OPE OPE.Orbits Spec Trace.Pilot
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
variable (F:Final C f S) (J:ℝ→PhysMS.tower S) (leading:PhysMS.Leading F J)
variable {K:(Bel C.book).Hierarchy}
variable (aligned:∀ d:ℕ,∀ᶠ r in trail,AlignO F.sector F.room.kernel.spin K d (J r d))

include aligned leading in
theorem present : Pier.Lair.Present F J := by
  refine ⟨?_,WilsonReportPrescribedTests.measured F J leading⟩
  intro m
  have raises (i j:Fin (m+1)) : ∀ᶠ r in trail,∀ h:i.val ≤ j.val,∀ x,
      J r j ((Maxwell.Free.scheme C.book.grid).rise h x)=F.sector.derivatives.rise h (J r i x) := by
    by_cases h:i.val ≤ j.val
    · exact (leading.raised h).mono fun _ row _=>row
    · exact Eventually.of_forall fun _ h'=> (h h').elim
  filter_upwards [eventually_all.mpr (fun i:Fin (m+1)=>aligned i),
    eventually_all.mpr (fun i=>eventually_all.mpr (raises i))] with r yes joined
  exact ⟨yes,joined⟩

variable {u:Filter (ℕ×ℕ)} (B:Mantle F u) (E:Services C f S) (L:Layout F)
variable (pegs:Pegs B L) (near:∀ᶠ r in trail,C.S.a (L.level r) ≤ r ∧
  r ≤ C.S.a (L.level r)*C.path.levels.clock.hatBeta (L.level r)^2)

include leading aligned E pegs near in
theorem original {I:Type*} [Fintype I] (d:I→ℕ) (v:(i:I)→Free C (d i)) (α:ℂ) :
    ∃ h:ℕ,∀ᶠ r in trail,∃ w:(i:I)→C.label (d i),∀ i,
      master L (d i) r (w i)=J r (d i) (v i) ∧
      mass C (d i) (α • L.shift (d i) r (w i)) ≤ C.path.levels.clock.hatBeta (L.level r)^h :=
  WilsonReportingMeasuredTender.roster B E (present F J leading aligned) pegs near d v α

end YM.Integration.WilsonReportingMeasuredAdmission
