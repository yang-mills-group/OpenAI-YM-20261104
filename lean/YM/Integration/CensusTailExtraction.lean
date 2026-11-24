import YM.Integration.CappedCensusFusion
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Weigh

/-! The scalar and kinetic counterterms actually extracted from a signed
vacuum source, including the finite-volume normalization of its constant. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CensusTailExtraction

open Filter Lattice Wilson RG Push.AbsoluteSums
open AnalyticBridge VerifiedReset Collection Averaging Quotes Residual
open IterationFour.Vacuum UVNext.CouplingReset

variable {G : Gauge} {n : Side} {p : BudgetPoint} {H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n}

/-- The signed sum at the identity is absolutely paid at the declared sites. -/
theorem constant (h : Local X p v H w) :
    SumBudget (fun i => |v.logRead i 1|) (sites n * H) := by
  obtain ⟨u,hu,hE⟩ := h.cheap
  have hsum := CouplingShape.totalBooked (p := p) (u := X.reg) (fun i => (hu i).1)
    (Quotes.segment X.reg (fun i => (hu i).1) hE)
  refine budget_mono hsum (fun i => abs_nonneg _) ?_
  intro i
  exact (hu i).2 1 (flat_ok p _) [] (by simp) (by simp)

/-- Both native counterterms are bounded by the same positive-order
source bill without a volume-dependent coefficient. -/
theorem extracted (g : G.Simple) (h : Local X p v H w) (W : PathData G) (c : Clip)
    (b τ : ℝ) :
    let Z := Reset.after W c p X v b τ 0
    Z.beta = b+delta (X.read v) ∧ Z.v = vac v τ ∧
    p.threshold^2*|Z.beta-b| ≤ H ∧ |Z.v-τ| ≤ H := by
  intro Z
  have hb : Z.beta = b+delta (X.read v) := by
    change b+0+delta (X.read v)=_
    rw [add_zero]
  have hs := constant h
  have hu : |∑' i, v.logRead i 1| ≤ sites n*H := by
    have hx := norm_tsum_le_tsum_norm (f := fun i => v.logRead i 1) hs.2.1
    exact hx.trans hs.2.2
  refine ⟨hb,rfl,?_,?_⟩
  · rw [hb,add_sub_cancel_left]
    exact delta_bound g h.projects
  · change |τ-(∑' i, v.logRead i 1)/sites n-τ| ≤ H
    rw [show τ-(∑' i, v.logRead i 1)/sites n-τ = -((∑' i, v.logRead i 1)/sites n) by ring,
      abs_neg,abs_div,abs_of_pos (sites_pos n), div_le_iff₀ (sites_pos n),mul_comm]
    exact hu

end YM.Integration.CensusTailExtraction
end
