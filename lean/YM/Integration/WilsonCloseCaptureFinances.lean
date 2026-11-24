import YM.Integration.WilsonLimitConstruction.FundedOriginalRun
import YM.RG05Readout.Capture.Invoices

/-! The signed multi-source cash and the complete replica storage on the chosen Wilson doors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCloseCaptureFinances
open Lattice RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Bandage
open WilsonLimitConstruction RG05Readout
universe u
variable {G : Gauge} (R : Run G) (hG : G.Simple)

theorem original {T : Campaign R} (W : Campaign.Pillars R T) {δ : ℝ}
    (fund : FundedOriginalProperties.{u} hG δ W) :
    Many.Storage R.family R.doors ∧ Cater R.family R.doors := by
  have order (m : ℕ) : 100 ≤ (R.alloy.B.a.budget m).supportExponent :=
    (fund.2.1.paid.fixed m).ge
  have shop := fund.2.2.2.2.2.2.1
  have ch := (R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have cash := escape R.b R.T shop.steam hG R.tuning.receipts shop.minty order R.doors (fun N p m hm => R.carries N m p hm)
  have same : Many.apron R.family.path.levels = mutt R.alloy.B.a (RG05Preconstruction.apronProfile R.rolls) := by
    funext i
    change Many.apron R.alloy.B.a i = _
    unfold Many.apron mutt RG05Preconstruction.apronProfile
    rw [Extra.Iteration.block_eq R.alloy.B.valid]
  refine ⟨⟨?_,shop.preMesh⟩,?_⟩
  · rw [same]
    exact cash
  · exact uv_RG05_cater hG R.b R.T R.Q R.t R.stories R.doors ch order shop.minty shop.accord

end YM.Integration.WilsonCloseCaptureFinances
