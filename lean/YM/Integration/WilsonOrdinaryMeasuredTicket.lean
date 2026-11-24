import YM.Integration.WilsonOrdinaryMeasuredMarch

/-! The complete literal RG12 exterior ticket, on the original observing layout, from
independent measured two-slot fixed-ratio tables for the positive physical grades. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryMeasuredTicket
open Filter Set Spec Climb OPE RG12 RG12.Frames RG17 SharpGram Trace.Pilot
open WilsonOrdinaryMeasuredMarch
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S)

theorem original (P : Pier.Lair.Present F J) (H : PhysMS.Leading F J)
    (g : ℝ → ℝ) (coupled : Coupling G g)
    (rows : ∀ d : ℕ, 4 ≤ d → ∃ (A B : Module.End ℂ ((Bel C.book).Field d)) (c : ℝ),
      0 ≤ c ∧ ResonantZero F d A ∧ MixedError F J d g A B c)
    {u : Filter (ℕ×ℕ)} (Q : Lenses.Mantle F u) (L : Layout F)
    (hL : Pegs Q L) (E : Services C f S) : OPE.Log.MatrixTicket (C:=C) S F.sector.derivatives L.lens := by
  letI := L.notbot
  obtain ⟨O,coh⟩ := OPE.Prescription.chosen F.room.kernel.laws.toSymmetric F.phase.transport.injection
  have priced (d : ℕ) : RightPrice C S L.charts d ∧ ∀ w, RowPrice C S F.sector.derivatives L.charts d w := by
    rcases lt_or_ge d 4 with low | high
    · exact ⟨low_right_price E.simpleGate L.observes S d low,fun w =>
        low_row_price E.simpleGate L.observes S F.sector.derivatives F.room.kernel.laws F.phase.transport.injection d w low⟩
    · obtain ⟨A,B,c,hc,zero,source⟩ := rows d high
      exact WilsonOrdinaryMeasuredMarch.prices F J d P H g coupled A B zero hc source O coh Q L hL E
  exact (satisfies_matrix_ticket E.simpleGate L.observes S F.sector.derivatives).2
    ⟨fun d => (priced d).1,fun d => (priced d).2⟩

end YM.Integration.WilsonOrdinaryMeasuredTicket
