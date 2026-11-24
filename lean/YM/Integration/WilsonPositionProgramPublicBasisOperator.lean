import YM.Integration.WilsonPositionProgramPublicFittedInverse

/-! A finite invoice on the original field columns controls the whole operator. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicBasisOperator
open Finset
open scoped BigOperators Classical
variable {I:Type*}[Fintype I]

theorem original (D:(I→ℂ)→L[ℂ](I→ℂ)) {k ρ E:ℝ} (hk:0≤k)
    (columns:∀i:I,k*(ρ*‖D (Pi.basisFun ℂ I i)‖)^2≤E):
    k*(ρ*‖D‖)^2≤(Fintype.card I:ℝ)^2*E:=by
  let a (i:I):=‖D (Pi.basisFun ℂ I i)‖
  have bound:‖D‖ ≤ ∑ i,a i:=by
    apply D.opNorm_le_bound (sum_nonneg fun _ _=>norm_nonneg _)
    intro x
    have dx:D x=∑ i,x i • D (Pi.basisFun ℂ I i):=by
      calc
        _ = D (∑ i,(Pi.basisFun ℂ I).repr x i • Pi.basisFun ℂ I i):=congrArg D ((Pi.basisFun ℂ I).sum_repr x).symm
        _ = _ :=by simp only [map_sum,map_smul,Pi.basisFun_repr]
    calc
      ‖D x‖ = ‖∑ i,x i • D (Pi.basisFun ℂ I i)‖ :=congrArg norm dx
      _ ≤ ∑ i,‖x i • D (Pi.basisFun ℂ I i)‖:=norm_sum_le ..
      _ ≤ ∑ i,a i*‖x‖:=Finset.sum_le_sum fun i _=>by
        rw [norm_smul,mul_comm];exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _)
      _ = _ :=by rw [Finset.sum_mul]
  have squares:(∑ i,a i)^2 ≤ (Fintype.card I:ℝ)*∑ i,(a i)^2:=by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq univ (fun _:I=>(1:ℝ)) a
  have fee (i:I):(k*ρ^2)*a i^2≤E:=by simpa only [a,mul_pow,mul_assoc] using columns i
  calc
    _ = (k*ρ^2)*‖D‖^2 :=by ring
    _ ≤ (k*ρ^2)*((Fintype.card I:ℝ)*∑ i,a i^2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hk (sq_nonneg _))
      exact (pow_le_pow_left₀ D.opNorm_nonneg bound 2).trans squares
    _ = (Fintype.card I:ℝ)*∑ i,(k*ρ^2)*a i^2:=by rw [←Finset.mul_sum];ring
    _ ≤ (Fintype.card I:ℝ)*∑ _:I,E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _=>fee i) (Nat.cast_nonneg _)
    _ = _ :=by simp;ring

end YM.Integration.WilsonPositionProgramPublicBasisOperator
