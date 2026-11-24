import YM.Integration.WilsonLimitConstruction.FundedOriginalRun
import YM.Integration.WilsonMatrixTicketLanesSeed

/-! Reconstruction, the first field comparison and the original table
observations all persist on the one quotient selected for strong estimates. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketLanesRetained
open Function Filter Spec Climb PhysicalNext.Repeat.Legato WilsonLimitConstruction
open Next.Extract Dash
universe u
variable {G : Gauge} {R : Run G} {T : Campaign R}

/-- All conclusions refer to the specified seed, its certified extraction and
its own quotient. In particular the representation of an MS prescription may
be calibrated on this same field table. -/
theorem original (simple : G.Simple) {ε : ℝ} (W : Campaign.Pillars R T)
    (account : FundedOriginalProperties.{u} simple ε W)
    (f : Extraction.Order) {A : Table R.family.book} {L : ℕ → Table R.family.book}
    {B : Bin A} {S : Table R.family.book} {E : DiffPlan S}
    (base : Base R.family f A L B S E) (seed : Seed R.family f S) :
    ∃ (F : Final R.family f S) (X : Scaling S) (a : EveryPhase.Almanac F)
      (reader : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin),
      F.sector.derivatives = E ∧ Pert.FirstExtension F X ∧
      EveryPhase.Completed F a ∧ Trace.Target.Result.{u} F simple ∧ Trace.Target.Exclusion.{u} F ∧
      OPE.Facilities R.family f S ∧ OPE.Orbits.Foundation F reader ∧ OPE.Nesting.Uniform F reader ∧
      (∀ q : OPE.Prescription F.sector.derivatives, q.Coherent → OPE.AllShapes F q) ∧
      (∀ U : Ultrafilter (ℕ × ℕ), (U : Filter _) ≤ f.fuse →
        Nonempty (SharpGram.Lenses.Mantle F (U : Filter _))) := by
  let broad := account.2.1
  obtain ⟨F,X,assign,service,first⟩ :=
    WilsonMatrixTicketLanesSeed.original R simple broad.logBudget.toPackage f base seed
  obtain ⟨a,completed⟩ := EveryPhase.all_characters F
  let t := F.phase.transport
  obtain ⟨p,hp⟩ := OPE.Prescription.chosen F.room.kernel.laws.toSymmetric t.injection
  let reader : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin :=
    ⟨p,hp,F.room.kernel,t.injection,t.rights,t.spots⟩
  have trace := broad.trace f S F
  exact ⟨F,X,a,reader,assign,first,completed,trace,trace.exclude,
    ⟨service,_,_,_,broad.logBudget⟩,OPE.Orbits.produce F reader service,
    OPE.Nesting.uniform F reader service,fun q hq => service.everything F q hq,
    fun U refines => SharpGram.Lenses.attains_mantle17 F service U refines broad.coverage⟩

end YM.Integration.WilsonMatrixTicketLanesRetained
