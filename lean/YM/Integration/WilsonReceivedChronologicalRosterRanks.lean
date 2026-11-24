import YM.Integration.WilsonOriginalReflectedFirstTerms
import YM.Integration.WilsonOriginalTwoFlatIRSocketPower
import YM.Integration.WilsonOriginalTwoFlatIRHalo

/-! Common finite orders for the two actual captured readings and every occupied subface. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterRanks
open Finset Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels Org AllOrder AllOrder.Floe
open WilsonReceivedChronologicalFixedReserve (terms)
open PhysicalNext.Repeat.Legato ActualRunAdmissionScales
open scoped BigOperators Classical
variable {G:Gauge}{n:ℕ}

def restored (n pole target:ℕ):ℕ:=target+2+2*pole*n

def crop (n goal:ℕ):ℕ:=goal+WilsonOriginalTwoFlatIRSocketPower.debt n 1
  (Fintype.card (Multi.Hot (Stock.census (Fin n))))

def infrared (d:Fin n→ℕ)(p:ℕ):ℕ:=4*(p+
  (WilsonOriginalTwoFlatIRHalo.power n ((∑i,d i)+1+2+(2+2*n*1))+0+2))

theorem original (R:Run G)(d:Fin n→ℕ)(pole target:ℕ):
    let money:=restored n pole target
    let Q:=crop n money
    let P:=WilsonOriginalReflectedFirstTerms.order R d Q+1
    money≤P ∧ Q≤(terms d (fun _=>0) P).order ∧
    money+WilsonOriginalTwoFlatIRSocketPower.debt n 1 (Fintype.card (Multi.Hot (Stock.census (Fin n))))≤Q+1 ∧
    0 < infrared d money ∧ ∀s:(Stock.census (Fin n)).Mode,
    4*(money+(WilsonOriginalTwoFlatIRHalo.power s.val.card ((∑i,d i)+1+2+(2+2*n*1))+0+2)) ≤ infrared d money:=by
  intro money Q P
  have crop_le:Q≤P:=Nat.le_succ_of_le (le_max_left Q _)
  have money_le:money≤Q:=Nat.le_add_right .. 
  refine ⟨money_le.trans crop_le,crop_le.trans (WilsonAddressedPublicFirstActivation.rank_budget d P),
    Nat.le_succ Q,?_,?_⟩
  · unfold infrared
    omega
  · intro s
    have size:s.val.card≤n:=by simpa only [Fintype.card_fin] using Finset.card_le_univ s.val
    unfold infrared WilsonOriginalTwoFlatIRHalo.power
    gcongr
end YM.Integration.WilsonReceivedChronologicalRosterRanks
end
