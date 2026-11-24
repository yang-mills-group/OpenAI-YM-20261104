import YM.Integration.WilsonMeasuredPublicCopies
import YM.Integration.WilsonMeasuredPublicCellGroup
import YM.Integration.WilsonMeasuredPublicLayout

/-! The complete signed and reflected original Wilson numerator on an admitted separated packet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicPacket
open Function Filter Set MeasureTheory Finset Table Lattice Wilson RG Cells Extraction Spec Climb OPE
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open WilsonMeasuredPublicSlots WilsonMeasuredPublicLayout WilsonMeasuredPublicCopies
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {l : Ultrafilter (ℕ×ℕ)} {I : Type} [Fintype I]
    {d : I → ℕ} {v : ∀i,S.Field (d i)} {s B:I → ℝ}
    (L:∀i,Slot F l (d i) (v i) (s i) (B i))
local notation "wage" => amount (F:=F) (B:=B) (s:=s) (v:=v)

theorem heard (q : ℕ×ℕ) (h:∀i,Cards.PaidAt R.family.S q.1 q.2 (L i).m (R.family.beta q.1 q.2)
        (wage i) (R.family.O q.1 q.2 ((L i).arm.source q) 0))
    (u : I → Site (R.family.side q.1 q.2)) (board : Placed R.family (fun i=>(L i).m) u) :
    (‖moment (R.family.beta q.1 q.2) (fun U=>∏i,field L q i (u i) U)‖≤∏i,wage i) ∧
    ∃ P : Config G (R.family.side q.1 q.2) → ℂ,
      board.wide.copy board.cell P=(fun U=>∏i,field L q i (u i) U) ∧
      Interior (board.wide.chamber 0) P ∧ board.wide.rootTest (R.family.beta q.1 q.2) P≤∏i,wage i ∧
      ‖moment (R.family.beta q.1 q.2) (board.wide.fullAt (fun _=>P))‖ ≤ (∏i,wage i)^Fintype.card board.wide.Cell := by
  have seam:=Cells.seamless F.room.cutoff q.1 q.2
  obtain ⟨P,same,own,price⟩ := WilsonMeasuredPublicCellGroup.exterior board.first board.second
    board.base board.subdiv u _ wage board.cell h board.divides board.together board.clearance board.separate seam
  have physical : board.wide.copy board.cell P=(fun U=>∏i,field L q i (u i) U) := by
    rw [same]
    funext U
    exact prod_congr rfl fun i _=>by rw [at_site L,(L i).actual]
  have one := board.wide.planted seam (fun _ : Unit=>board.cell) (fun _ _ _=>Subsingleton.elim _ _)
    (fun _=>P) (fun _=>own)
  have single : ‖moment (R.family.beta q.1 q.2) (board.wide.copy board.cell P)‖≤board.wide.rootTest (R.family.beta q.1 q.2) P := by
    simpa using one
  refine ⟨physical ▸ single.trans price,P,physical,own,price,?_⟩
  change board.wide.rootPower (R.family.beta q.1 q.2) (fun _=>P) ≤ _
  rw [← board.wide.powering]
  exact pow_le_pow_left₀ (board.wide.root_nonneg ..) price _

end YM.Integration.WilsonMeasuredPublicPacket
