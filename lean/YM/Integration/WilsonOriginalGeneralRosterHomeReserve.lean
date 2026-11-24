import YM.Integration.WilsonOriginalGeneralRosterHomeMenu

/-! The reserve for the complete menu is determined by stock, grades,
multiplicity and requested accuracy. Each physical diagnostic test may
subsequently be filled with the majorant that the shared reserve buys. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeReserve
open Finset Function Wilson Lattice Extraction Table
open WilsonOriginalGeneralRosterUnion (Row need)
open WilsonOriginalGeneralRosterHomeMenu (menu)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open scoped BigOperators Classical
variable {I B:Type}[Fintype I][Fintype B]{D:ℕ}
def amount (T h:ℕ)(d:I→Fin (D+1))(E:I→ℕ)(main:Row I)(ψ:Fin main.size→Test 2)
    (p:Fin main.size→ℕ)(outside:B→Row I):ℕ:=by
  classical
  exact depth ((2*(univ.sup (need d E (menu main ψ p outside))+1)+∑i,E i)+1) (width T h) D

theorem positive (T h:ℕ)(d:I→Fin (D+1))(E:I→ℕ)(main:Row I)(ψ:Fin main.size→Test 2)
    (p:Fin main.size→ℕ)(outside:B→Row I):0 < amount T h d E main ψ p outside:=by
  unfold amount depth
  positivity

theorem same (T h:ℕ)(d:I→Fin (D+1))(E:I→ℕ)(main:Row I)(ψ χ:Fin main.size→Test 2)
    (p:Fin main.size→ℕ)(outside:B→Row I):amount T h d E main ψ p outside=amount T h d E main χ p outside:=by
  classical
  have fixed:need d E (menu main ψ p outside)=need d E (menu main χ p outside):=by
    funext i
    unfold need
    apply Finset.sup_congr rfl
    intro w _
    rcases w with _ | u
    · rfl
    · cases u <;> rfl
  unfold amount
  rw [fixed]

end YM.Integration.WilsonOriginalGeneralRosterHomeReserve
end
