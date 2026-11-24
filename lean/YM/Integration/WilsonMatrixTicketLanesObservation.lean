import YM.RG17.Layout

/-! Retain the original reporting filter and every one of its chart limits
when its physical ticket was first purchased on a common refinement. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketLanesObservation
open Filter RG12 RG17

variable {G : Gauge} {C : Family G} {F : Extraction.Order} {S : Table C.book}
  {Z : Spec.Final C F S} {P : DiffPlan S}

/-- The inlet and outlet on a subfilter price precisely the same two families
of chart matrices as on the full layout. -/
theorem on_layout (simple : G.Simple) (L : Layout Z) {f : Filter UVIndex} [f.NeBot]
    (refines : f ≤ L.lens) (bought : OPE.Log.MatrixTicket (C := C) S P f) :
    OPE.Log.MatrixTicket (C := C) S P L.lens := by
  letI := L.notbot
  have observed : Observing C Z.room.cutoff f L.charts :=
    ⟨L.observes.grows.mono_left refines,
      fun d k h => (L.observes.tends d k h).mono_left refines⟩
  exact (satisfies_matrix_ticket simple L.observes S P).2
    ((satisfies_matrix_ticket simple observed S P).1 bought)

end YM.Integration.WilsonMatrixTicketLanesObservation
