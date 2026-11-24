import YM.Extra.FREE_DETECTOR_ALGEBRA.Dialog
import YM.Extra.FREE_DETECTOR_ALGEBRA.LegAct
import YM.Extra.FREE_DETECTOR_ALGEBRA.LabelTurn

set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Labels
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {F M : Type*} [NormedAddCommGroup F] [NormedAddCommGroup M] {j : ℕ}

variable {G : Gauge}

theorem spin_projection (s : Ortho) (A : TwoJet G.Color j) : solAct s (asSol A)=asSol (carry s A) := by
  apply (dualSol G.Color j).injective; ext q
  have h : q = solAct s (solAct s⁻¹ q) := by rw [← solAct_mul,mul_inv_cancel,solAct_id]
  rw [h,asSol_duality,dualSol_val]
  let V := solAct s⁻¹ q
  change dotF (carry s (asSol A).val) (carry s V.val) = dotF (carry s A) (carry s V.val)
  rw [carry_dot,carry_dot]; exact asSol_duality A V

theorem send_spin (s : Ortho) (p : Taylor G j) : sendTo G j (Taylor.turn s p)=solAct s (sendTo G j p) := by
  change asSol (takeCurl _) = _; rw [takeTurn,← spin_projection]; rfl

end YM.Extra.FD
