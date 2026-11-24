import YM.Integration.FVA1Physical.Marked.PhysicalStencil

/-! Gauge-legal native marked operands for monomials of the independently
specified bare fields. The finite Haar cubature and all loop lengths are
fixed without reference to the period, field, cutoff or external sources. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Stationary Marker Qlocal Qlocal.Quipu Qlocal.Quipu.Sonnet Qlocal.Quipu.Lasso Qlocal.Quipu.Zora MeasureTheory
open scoped Classical BigOperators
variable {G : Gauge} {n : ℕ} {c : Side} {I : Type} [DecidableEq I] {B : Census I}

def invariantOperand (s : Senses B) (S : Fin n→RG.Slot) (j : Ink G n) : Vase s G n where
  stage := default
  ink := (Classical.choice (Zora.born G n)).forecast j
  maps i := Wand.squarely (S i)
  tan _ := false
  legal := (Classical.choice (Zora.born G n)).funded j le_rfl

theorem invariant_operand_eq (s : Senses B) (S : Fin n→RG.Slot) (j : Ink G n)
    (x : Site c) (q : ℕ) (v : Config G c) :
    (invariantOperand s S j).read x q v =
      ∫ u : G.El, ∏ i, G.adjoint u ((S i).atSite v x) (j i) ∂G.probHaar := by
  rw [Vase.globe]
  let Y := Classical.choice (Zora.born G n)
  change (∑ k : Ink G n, Y.forecast j k * Noon.bump k
    (fun i => G.curvature (travel v x (Work.F02.slotWalk (S i))))) = _
  simp_rw [← Work.F02.atSite_curvature]
  exact (Y.focused j _).trans (Y.hours j _ le_rfl)

def operandCost (s : Senses B) (S : Fin n→RG.Slot) : ℕ :=
  (∑ i : Fin n, (1 + (Work.F02.slotWalk (S i)).length)) + (default : Bay s).tariff

theorem invariant_operand_price (s : Senses B) (S : Fin n→RG.Slot) (j : Ink G n) (width : ℝ) :
    (invariantOperand s S j).fare width ≤ Noon.bill G (Classical.choice (Zora.born G n)) n * Real.exp (width*(operandCost s S : ℝ)) := by
  unfold Vase.fare
  exact mul_le_mul_of_nonneg_right (Noon.bill_ge _) (Real.exp_pos _).le

end YM.Integration.FVA1Physical.Marked
