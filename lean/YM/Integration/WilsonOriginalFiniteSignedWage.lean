import YM.Integration.WilsonOriginalCoveredMixedRoster

/-! Regroup a countable signed physical roster into finitely many tested components under its single original expense. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiniteSignedWage
open Filter Finset Function RG Push.AbsoluteSums
open scoped Classical BigOperators Topology
variable {I X:Type*} [Fintype X]

theorem original (a:X→ℝ) (cost:∀x,0≤a x) (m:I→X→ℂ) (read:X→ℂ)
    (paid:∀x,HasSum (fun i=>m i x) (read x)) {M:ℝ}
    (funds:SumBudget (fun y:Σ _:I,X=>a y.2*‖m y.1 y.2‖) M):
    (∑x,a x*‖read x‖)≤M:=by
  have heard:Tendsto (fun s:Finset I=>∑x:X,a x*‖∑i∈s,m i x‖) atTop (𝓝 (∑x:X,a x*‖read x‖)):=by
    apply tendsto_finsetSum
    intro x _
    exact (paid x).norm.const_mul (a x)
  apply le_of_tendsto heard
  refine Eventually.of_forall fun s=>?_
  calc
    _ ≤ ∑x:X,∑i∈s,a x*‖m i x‖:=by
      apply sum_le_sum
      intro x _
      rw [←mul_sum]
      exact mul_le_mul_of_nonneg_left (norm_sum_le ..) (cost x)
    _ = ∑i∈s,∑x:X,a x*‖m i x‖:=sum_comm
    _ ≤ M:=by
      have B:=(funds.2.1.sum_le_tsum (s.sigma fun _=>univ) (fun y _=>funds.1 y)).trans funds.2.2
      simpa only [sum_sigma'] using B

end YM.Integration.WilsonOriginalFiniteSignedWage
