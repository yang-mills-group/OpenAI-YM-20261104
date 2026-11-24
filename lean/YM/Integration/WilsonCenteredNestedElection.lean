import YM.Integration.WilsonCenteredNestedPhysical
import YM.Integration.WilsonMacroscopicFundedReader

/-! Preserve the actual logarithmic matrix and the measured OPE reader,
field frame and marked cohort before taking any nested orders. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonCenteredNestedElection
open OPE OPE.Orbits OPE.Log Spec Filter Climb Trace.Pilot PhysMS PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple)

/-- On the very ticket already selected by the original election. Raw
logarithmic tree comparisons at Q.port and the public power-loss tree
comparisons on Q are both retained. -/
theorem on_ticket {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (fac : Facilities R.family f S) (l : Ultrafilter (ℕ×ℕ)) (lo : (l : Filter _) ≤ f.fuse)
    (matrix : MatrixTicket (C:=R.family) S F.sector.derivatives (l : Filter _)) :
    Nesting.Uniform F Q ∧ LogTrace F Q.port :=
  ⟨Nesting.uniform F Q fac.toServices,OPE.tickets_suffice F fac lo matrix Q.spans⟩

theorem original {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (funded : WilsonMacroscopicFundedReader.Elected.{u} R simple cohort) (v : Extraction.Order) :
    ∃ (w : Extraction.Order) (S : Table R.family.book) (F : Final R.family (v.refine w) S)
      (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
      (Y : (Bel R.family.book).Hierarchy) (Z : Trace.Terrace.Arch R.family) (l : Ultrafilter (ℕ×ℕ))
      (J : ℝ → PhysMS.tower S),
      Facilities R.family (v.refine w) S ∧ Foundation F Q ∧ Bliss F l Z Y ∧ Leading F J ∧
      (∀ d,∀ᶠ r in trail,Frame.obedient F Y (J r) d) ∧
      (l : Filter _) ≤ (v.refine w).fuse ∧ cohort l ∧
      MatrixTicket (C:=R.family) S F.sector.derivatives (l : Filter _) ∧
      Nesting.Uniform F Q ∧ LogTrace F Q.port := by
  obtain ⟨w,S,F,_,Q,_,_,_,fac,foundation,_,Y,Z,l,bliss,_,_,J,_,_,_,_,_,_,_,
    lead,obedient,lo,selected,matrix⟩ := funded v
  exact ⟨w,S,F,Q,Y,Z,l,J,fac,foundation,bliss,lead,obedient,lo,selected,matrix,
    on_ticket R F Q fac l lo matrix⟩

end YM.Integration.WilsonCenteredNestedElection
