import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7JointWeakBookPrices
import YM.WilsonCoeffUV.Vacuum.UV.Budget

set_option autoImplicit false
noncomputable section
namespace PhysicalMatching.H7OriginalWeakBookBudget
open YM YM.Integration
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open Push.PriceCompiler ThroughLaunch WilsonLimitConstruction.FundedCompanySelection
open WilsonFundedWindowMenu WilsonWindowJointPurchase Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank
open H7JointWeakBookPrices
variable {G : Gauge}

def prediction (c : Costs G) : Prediction G :=
  @budget G c (fun s => Ticket.floors G s.kernel id)
    (fun {_} D => Ticket.voucher D id (chart G))

theorem paid (c : Costs G) : AllPrices (@prediction G c) :=
  purchase c (fun s => Ticket.floors G s.kernel id) (fun _ _ => rfl)
    (fun {_} D => Ticket.voucher D id (chart G))

theorem amounts (c : Costs G) (R : Run G) (earned : prediction c R.kit) :
    R.metals.O = chart G ∧
    (∀ j, max (Ticket.floors G R.metals.p.kernel id j)
      (Nat.ceil ((2 + c.pre R.metals.p j) ^ (j ^ 2))) ≤ R.metals.p.floorL j) ∧
    (∀ j, max (Ticket.voucher R.rolls id R.metals.O j)
      (Real.exp (Real.exp (2 + c.post R.rolls j))) ≤ R.alloy.delay.betaEntry j) := by
  obtain ⟨eq,first,last⟩ := earned
  exact ⟨eq,first,by rw [eq]; exact last⟩

end PhysicalMatching.H7OriginalWeakBookBudget
end
