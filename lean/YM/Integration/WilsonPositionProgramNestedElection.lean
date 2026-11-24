import YM.Integration.WilsonPositionProgramElection
import YM.Integration.WilsonPositionProgramNestedLengths
import YM.RegulatorIR.Atlas.Shelves

/-! Select the formal infrared closure and its kinetic floors with the original matrix ticket. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramNestedElection
open Filter Lattice RG Wilson RG.Supply Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch
open OPE OPE.Owl Next.Foundations Roost
open ThroughLaunch Roof Push.PriceCompiler Progress.DirectedRecipe
open WilsonMatrixTicketLengths WilsonMatrixTicketLengthsLender WilsonMatrixTicketFuelPrice
open WilsonLimitConstruction.FundedCompanySelection RegulatorIR
open scoped Classical Topology BigOperators
variable {G : Gauge} {a : Axis} {ε : ℝ}

def floor (G : Gauge) (K : KernelChoices) (j : ℕ) : ℕ := 16 +
  ∑ p ∈ Finset.range (j+1), ∑ u ∈ Finset.range (j+1),
    Atlas.orders G (Oracle.books K) p u j (1/2) (by norm_num) (by norm_num)

theorem sufficient (K : KernelChoices) {j p u : ℕ} (hp : p ≤ j) (hu : u ≤ j) :
    Atlas.orders G (Oracle.books K) p u j (1/2) (by norm_num) (by norm_num) ≤ floor G K j := by
  let c := fun i b => Atlas.orders G (Oracle.books K) i b j (1/2) (by norm_num) (by norm_num)
  have inner := Finset.single_le_sum (f:=c p) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hu))
  have outer := Finset.single_le_sum (f:=fun i => ∑ b ∈ Finset.range (j+1), c i b)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hp))
  exact (inner.trans outer).trans (Nat.le_add_left _ _)

def course (simple : G.Simple) (a : Axis) (ε : ℝ) : Prediction G := fun {M} {D} {_} F =>
  Eligible simple a ε F ∧ WilsonPositionProgramNestedLengths.Nested D ∧ ∀ n, floor G M.p.kernel n ≤ (D.L n).val

theorem prior {M : Metals G} {D : Rolls M.p} {A : Alloy M D} {F : Factor A} {simple : G.Simple}
    (paid : course simple a ε F) : WilsonPositionProgramElection.course simple a ε F :=
  ⟨paid.1,WilsonPositionProgramNestedLengths.divides paid.2.1⟩

/-- The original prices and the independently declared variable-circuit floors use one election. -/
theorem funded (simple : G.Simple) (finance : Glacier (a:=a) simple ε) :
    WilsonMatrixTicketLengthsLender.Supply G (@course G simple a ε) := by
  intro K branches v draft C hC
  obtain ⟨offer⟩ := available simple branches draft C hC
  let pad : Spells.Pad G := Classical.choice (Spells.curtainL G)
  let approved (k : ℕ → ℕ) (U : Rolls (raise offer.sheet k)) :=
    (∃ desk : Desk (raise offer.sheet k) offer.ledger a simple, FrameBill desk U) ∧
      WilsonPositionProgramNestedLengths.Nested U ∧ ∀ j, floor G offer.sheet.kernel j ≤ (U.L j).val
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
    obtain ⟨desk⟩ := Desk.from_a offer.season offer.ledger (raise offer.sheet k) deep a simple
    obtain ⟨U,frame,hU⟩ := WilsonPositionProgramNestedLengths.elect desk
    exact ⟨U,⟨desk,frame⟩,hU,fun j => (wide j).trans (U.large j).need⟩
  · intro k U ok books P θ V
    obtain ⟨desk,frame⟩ := ok.1
    obtain ⟨W,later,receipt⟩ := WilsonMatrixTicketFuelPrice.buy desk pad finance frame books θ V
    exact ⟨W,later,fun Y since => ⟨desk,receipt Y since⟩⟩
  · intro k U P θ V bar W priced B F ok kinetic cash
    obtain ⟨desk,row⟩ := cash
    have size (j : ℕ) : 16 ≤ (U.L j).val := (Nat.le_add_right 16 _).trans (ok.2.2 j)
    exact ⟨WilsonMatrixTicketFuelPrice.deliver F offer.issued size kinetic row,ok.2⟩

end YM.Integration.WilsonPositionProgramNestedElection
end
