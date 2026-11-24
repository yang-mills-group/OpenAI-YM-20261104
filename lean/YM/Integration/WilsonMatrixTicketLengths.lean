import YM.Integration.WilsonMatrixTicketLengthsSponsor
import YM.OPE.Compatible.Niche.Expat

/-! On the real retained sheet, elect the block lengths meeting every issued frame and current floor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLengths
open Function Filter Lattice RG Source Wilson Precision RG.Supply Input
open PhysicalNext PhysicalNext.ThroughLaunch Further.StrongStartup Extra.Histories
open Next.Foundations Org OPE OPE.Owl
open scoped Topology BigOperators Classical
variable {G : Gauge}

variable {K : KernelChoices} {v : Orders} {C : ℕ → ℝ}

/-- Once every pre-length floor is known, buy one block sequence on that
raised sheet. At every active level it is a power of each requested
frame base. Its actual side simultaneously clears every floor already
charged in `k`. -/
theorem choose (offer : Offer G K v C) (simple : G.Simple) (plan : Draft v)
    (k : ℕ → ℕ) (a : Axis) :
    ∃ (D : Desk (raise offer.sheet k) offer.ledger a simple)
      (P : Rolls (raise offer.sheet k)), FrameBill D P ∧
      ∀ j, k j ≤ (P.L j).val := by
  have deep : Tendsto (fun j => (offer.sheet.profile j).order) atTop atTop :=
    tendsto_atTop_mono (f:=id) (g:=_) (fun j => by
      rw [offer.stage.jets]; exact (le_max_right ..).trans (plan.k j)) tendsto_id
  obtain ⟨D⟩ := Desk.from_a offer.season offer.ledger (raise offer.sheet k) deep a simple
  obtain ⟨P, good⟩ := Desk.enrich D
  exact ⟨D,P,good,fun j => (P.large j).need⟩

end YM.Integration.WilsonMatrixTicketLengths
