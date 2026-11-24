import YM.Integration.WilsonOriginalNamedCompactCover
import YM.Integration.WilsonOriginalPointCompactRoster

/-! Exact relative copies of the original occupied inputs before conditional integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCarriedDeckForms
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder.Floe Comparison.RG02
open FVA1Physical FVA1Physical.TwoReset Multi
open scoped Classical BigOperators
variable {G:Gauge} {n f:Side} {V ι α:Type} [DecidableEq V] {o:Passport n V} {C:Census V}
  (h:n.val ∣ f.val) (M:ι→Row o C G α) (grades:V→ℕ) (ink:ι→ℂ) (quiet:Layout G) (tape:Finset Age)
local notation "W" => FVA1Physical.TwoReset.copyColor h M grades ink quiet tape
local notation "leaf" v:max => Air.craft (fun j:ι=> FVA1Physical.TwoReset.copy h (M j) v) ink grades quiet tape

/-- Each named row is placed on the actual fiber of its original center on the enlarged lattice. -/
theorem center (j:ι) (p:Fin (Pages n f)) :
    (FVA1Physical.TwoReset.copy h (M j) p).center=(page h (M j).center p).val := rfl

theorem letter (j:ι) (g:ℝ) (U:Config G f) :
    FVA1Physical.TwoReset.copiesLetter h M j g U=
      ∑p:Fin (Pages n f),((Loan.letter (M j).lamp (M j).atom
        (page h (M j).center p).val g U:ℝ):ℂ) := by
  exact (FVA1Physical.TwoReset.pages h (M j).center
    (fun y=>((Loan.letter (M j).lamp (M j).atom y g U:ℝ):ℂ))).symm

/-- In particular the two operands may be the deposited AB and the still-present C.
The index of the copy on the first operand remains free from the index on the second. -/
theorem occupied {L:Type} [Fintype L] [DecidableEq L] (cuts:L→Hot C) (g:ℝ) (U:Config G f) :
    (∏v:L,(W).mark (cuts v) g U)=
      ∑p:L→Fin (Pages n f),∏v:L,(leaf (p v)).mark (cuts v) g U := by
  simpa only [FVA1Physical.TwoReset.copyColor,Finset.sum_apply] using
    (Fintype.prod_sum (fun (v:L) (b:Fin (Pages n f))=>(leaf b).mark (cuts v) g U))

end YM.Integration.WilsonOriginalCarriedDeckForms
