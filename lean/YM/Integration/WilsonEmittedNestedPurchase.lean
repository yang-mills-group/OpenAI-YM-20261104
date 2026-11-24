import YM.Integration.WilsonPositionProgramNestedElection

/-! The original sponsor can choose the factorial block lengths and their
formal infrared floors before the cutoff, independently of the null-field fare. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedNestedPurchase
open Filter Lattice RG Wilson RG.Supply Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch
open OPE OPE.Owl Next.Foundations Roost
open ThroughLaunch Roof Push.PriceCompiler Progress.DirectedRecipe
open WilsonMatrixTicketLengths WilsonMatrixTicketLengthsLender WilsonMatrixTicketFuelPrice
open WilsonLimitConstruction.FundedCompanySelection RegulatorIR
open scoped Classical Topology BigOperators
variable {G : Gauge} {a : Axis} {ε : ℝ}

open WilsonPositionProgramNestedElection

def Geometry : Prediction G := fun {M} {D} {_} _ =>
  WilsonPositionProgramNestedLengths.Nested D ∧ ∀ n, floor G M.p.kernel n ≤ (D.L n).val

theorem funded (simple : G.Simple) (axis : Axis) :
    WilsonMatrixTicketLengthsLender.Supply G (@Geometry G) := by
  intro K branches v draft C hC
  obtain ⟨offer⟩ := available simple branches draft C hC
  let accepted (k : ℕ → ℕ) (U : Rolls (raise offer.sheet k)) :=
    WilsonPositionProgramNestedLengths.Nested U ∧ ∀ j, floor G offer.sheet.kernel j ≤ (U.L j).val
  let issued {k : ℕ → ℕ} {U : Rolls (raise offer.sheet k)}
      (_ : Arms (M:=bountyV offer.sheet offer.price k) U) (_ : PostCost U)
      {θ : Protection U} (_ : Delays θ) : Prop := True
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
    allowed := accepted
    floor := floor G offer.sheet.kernel
    select := ?_
    paid := @issued
    buy := ?_
    deliver := ?_ }⟩
  · intro k wide
    have deep : Tendsto (fun j => ((raise offer.sheet k).profile j).order) atTop atTop := by
      apply tendsto_atTop_mono _ tendsto_id
      intro j
      change j ≤ (offer.sheet.profile j).order
      rw [offer.stage.jets]
      exact (le_max_right ..).trans (draft.k j)
    obtain ⟨desk⟩ := Desk.from_a offer.season offer.ledger (raise offer.sheet k) deep axis simple
    obtain ⟨U,_,hU⟩ := WilsonPositionProgramNestedLengths.elect desk
    exact ⟨U,hU,fun j => (wide j).trans (U.large j).need⟩
  · intro k U ok books P θ V
    exact ⟨V,DelayLe.refl _,fun _ _=>True.intro⟩
  · intro k D P θ V b W priced B X ok _ _
    exact ok

end YM.Integration.WilsonEmittedNestedPurchase
