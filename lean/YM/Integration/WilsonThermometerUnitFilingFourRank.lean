import YM.RG12.Kintsugi.Outlet

/-! The original raw grade-four sampling space and its Maxwell quotient have
the same 22 entries, with the empty sector giving the unit. -/

noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourRank

open Function Set UVNext.FreeStress
open Labels Maxwell Climb Table

variable {G : Gauge} (C : Family G) (hG : G.Simple)

include hG in
theorem original : Fintype.card (C.labels.level 4).Index = 22 := by
  let b : Module.Basis (Option Face) ℂ (Labels.Label G 4) :=
    Module.Basis.mk (LinearIndependent.of_comp (embed C.book.grid 4)
      (freelance C.book.grid hG)) (up_to hG)
  calc
    _ = Module.finrank ℂ (Labels.Label G 4) :=
      (Module.finrank_eq_card_basis (C.labels.level 4).basis).symm
    _ = Fintype.card (Option Face) := Module.finrank_eq_card_basis b
    _ = 22 := howMany

theorem unit : (C.labels.level 4).basis 0 = Labels.unit G 4 :=
  (C.labels.level 4).starts_unit

end YM.Integration.WilsonThermometerUnitFilingFourRank

