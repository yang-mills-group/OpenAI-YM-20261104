import YM.Integration.WilsonPositionScaleLawGuardLipschitz

/-! A bound on the printed coefficients controls the entire polynomial on
the original unit disk and its movement from its rooted scalar value. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardValue
open Finset PowerSeries
open WilsonPositionScaleLawGuardPoly (value)
open WilsonPositionScaleLawGuardLipschitz (slope)
open scoped Polynomial Classical BigOperators
variable {R:Type*}[NormedRing R][NormedAlgebra ℂ R]

theorem count (q:ℕ):Finset.Iic q=range (q+1):=by ext n;simp only [Finset.mem_Iic,Finset.mem_range];omega

theorem original (q:ℕ)(a:PowerSeries R){C:ℝ}(h:∀j≤q,‖coeff j a‖≤C){z:ℂ}(hz:‖z‖≤1):
    ‖value (trunc (q+1) a) z‖≤((q+1:ℕ):ℝ)*C:=by
  rw [WilsonPositionScaleLawGuardEval.printed]
  calc
    _≤∑j∈Finset.Iic q,‖z^j • coeff j a‖:=norm_sum_le _ _
    _≤∑_∈Finset.Iic q,C:=by
      apply Finset.sum_le_sum;intro j hj
      rw [norm_smul,norm_pow]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)).trans (h j (Finset.mem_Iic.mp hj))
    _=_:=by rw [count];simp [nsmul_eq_mul]

omit [NormedAlgebra ℂ R] in
theorem sliding (q:ℕ)(a:PowerSeries R){C:ℝ}(hC:0≤C)(h:∀j≤q,‖coeff j a‖≤C):
    slope q a≤((q+1:ℕ):ℝ)*((q:ℝ)*C):=by
  calc
    _≤∑_∈Finset.Iic q,(q:ℝ)*C:=by
      apply Finset.sum_le_sum;intro j hj
      exact (mul_le_mul_of_nonneg_left (h j (Finset.mem_Iic.mp hj)) (Nat.cast_nonneg j)).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.mem_Iic.mp hj) hC)
    _=_:=by rw [count];simp [nsmul_eq_mul]

theorem zero (q:ℕ)(a:PowerSeries ℂ)(h:coeff 0 a=0):
    value (trunc (q+1) a) (0:ℂ)=0:=by
  rw [WilsonPositionScaleLawGuardEval.printed]
  apply Finset.sum_eq_zero
  intro k _
  by_cases e:k=0
  · subst k;rw [h,smul_zero]
  · rw [zero_pow e,zero_smul]

theorem scalar (q:ℕ)(a:PowerSeries ℂ)(root:coeff 0 a=0){C:ℝ}(hC:0≤C)(h:∀j≤q,‖coeff j a‖≤C)
    {z:ℂ}(hz:‖z‖≤1):‖(trunc (q+1) a).eval z‖≤(((q+1:ℕ):ℝ)*((q:ℝ)*C))*‖z‖:=by
  have move:=WilsonPositionScaleLawGuardLipschitz.original q a z 0 hz (by simp)
  rw [zero q a root,sub_zero,sub_zero] at move
  exact move.trans (mul_le_mul_of_nonneg_right (sliding q a hC h) (norm_nonneg _))

end YM.Integration.WilsonPositionScaleLawGuardValue
