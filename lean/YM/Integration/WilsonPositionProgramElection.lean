import YM.Integration.WilsonPositionProgramLengths
import YM.Integration.WilsonMatrixTicketLengthsClock
import YM.Integration.WilsonMatrixTicketFuelPrice

/-! Co-elect the common position-regulator lengths with the original matrix and null-field finances. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramElection
open Filter Lattice RG Wilson RG.Supply Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch
open OPE OPE.Owl Next.Foundations Roost
open ThroughLaunch Roof Push.PriceCompiler Progress.DirectedRecipe
open WilsonMatrixTicketLengths WilsonMatrixTicketLengthsLender WilsonMatrixTicketFuelPrice
open WilsonLimitConstruction.FundedCompanySelection
open scoped Classical Topology
variable {G : Gauge} {a : Axis} {ε : ℝ}

def course (simple : G.Simple) (a : Axis) (ε : ℝ) : Prediction G := fun {_} {D} {_} F =>
  Eligible simple a ε F ∧ WilsonPositionProgramLengths.Divisible D

/-- Select a single genuine roll after quoting all pre-length costs, before the physical run. -/
theorem select {K : KernelChoices} {v : Orders} {C : ℕ → ℝ} (offer : Offer G K v C)
    (simple : G.Simple) (plan : Draft v) (k : ℕ → ℕ) (a : Axis) :
    ∃ (D : Desk (raise offer.sheet k) offer.ledger a simple) (P : Rolls (raise offer.sheet k)),
      FrameBill D P ∧ WilsonPositionProgramLengths.Divisible P ∧ ∀ j, k j ≤ (P.L j).val := by
  have deep : Tendsto (fun j => ((raise offer.sheet k).profile j).order) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro j
    change j ≤ (offer.sheet.profile j).order
    rw [offer.stage.jets]
    exact (le_max_right ..).trans (plan.k j)
  obtain ⟨D⟩ := Desk.from_a offer.season offer.ledger (raise offer.sheet k) deep a simple
  obtain ⟨P,frame,lengths⟩ := WilsonPositionProgramLengths.elect D
  exact ⟨D,P,frame,lengths,fun j => (P.large j).need⟩

/-- All matrix and null-field invoices and the retained exponent choice go through the same auction. -/
theorem funded (simple : G.Simple) (finance : Glacier (a:=a) simple ε) :
    WilsonMatrixTicketLengthsLender.Supply G (@course G simple a ε) := by
  intro K branches v draft C hC
  obtain ⟨offer⟩ := available simple branches draft C hC
  let pad : Spells.Pad G := Classical.choice (Spells.curtainL G)
  let approved (k : ℕ → ℕ) (U : Rolls (raise offer.sheet k)) :=
    (∃ desk : Desk (raise offer.sheet k) offer.ledger a simple, FrameBill desk U) ∧
    (∀ j, 16 ≤ (U.L j).val) ∧ WilsonPositionProgramLengths.Divisible U
  let issued {k : ℕ → ℕ} {U : Rolls (raise offer.sheet k)}
      (books : Arms (M:=bountyV offer.sheet offer.price k) U) (P : PostCost U)
      {θ : Protection U} (V : Delays θ) : Prop :=
    ∃ desk : Desk (raise offer.sheet k) offer.ledger a simple,
      WilsonMatrixTicketFuelPrice.Paid desk pad ε books θ V
  refine ⟨{
    sheet := offer.sheet
    firstPrice := offer.sponsor.X
    price := offer.price
    clock := offer.sponsor.l
    slope := offer.slope
    worth := offer.worth
    kernel := offer.kernel
    stage := offer.stage
    invoices := offer.invoices
    allowed := approved
    floor := fun _ => 16
    select := ?_
    paid := @issued
    buy := ?_
    deliver := ?_ }⟩
  · intro k wide
    obtain ⟨desk,U,frame,lengths,hk⟩ := select offer simple draft k a
    exact ⟨U,⟨desk,frame⟩,fun j => (wide j).trans (hk j),lengths⟩
  · intro k U ok books P θ V
    obtain ⟨⟨desk,frame⟩,_⟩ := ok
    obtain ⟨W,later,receipt⟩ := WilsonMatrixTicketFuelPrice.buy desk pad finance frame books θ V
    exact ⟨W,later,fun Y since => ⟨desk,receipt Y since⟩⟩
  · intro k U P θ V bar W priced B F ok kinetic cash
    obtain ⟨desk,row⟩ := cash
    exact ⟨WilsonMatrixTicketFuelPrice.deliver F offer.issued ok.2.1 kinetic row,ok.2.2⟩

end YM.Integration.WilsonPositionProgramElection
end
