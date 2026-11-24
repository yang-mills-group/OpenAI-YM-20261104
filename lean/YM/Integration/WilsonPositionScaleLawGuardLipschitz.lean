import YM.Integration.WilsonPositionScaleLawGuardEval

/-! The finite modulus of the prescribed correction on the complex unit disk. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardLipschitz
open Finset PowerSeries
open WilsonPositionScaleLawGuardPoly (value)
open scoped Polynomial Classical BigOperators

theorem power (z w:ℂ)(hz:‖z‖≤1)(hw:‖w‖≤1)(k:ℕ):‖z^k-w^k‖≤(k:ℝ)*‖z-w‖:=by
  induction k with
  | zero=>simp
  | succ k ih=>
    have small:‖z^k‖≤1:=by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) hz
    have eq:z^(k+1)-w^(k+1)=z^k*(z-w)+(z^k-w^k)*w:=by ring
    rw [eq]
    calc
      _≤‖z^k*(z-w)‖+‖(z^k-w^k)*w‖:=norm_add_le _ _
      _=‖z^k‖*‖z-w‖+‖z^k-w^k‖*‖w‖:=by rw [norm_mul,norm_mul]
      _≤1*‖z-w‖+(k:ℝ)*‖z-w‖*1:=add_le_add (mul_le_mul_of_nonneg_right small (norm_nonneg _))
          (mul_le_mul ih hw (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))
      _=_:=by push_cast;ring

variable {R:Type*}[NormedRing R][NormedAlgebra ℂ R]
def slope (q:ℕ)(A:PowerSeries R):ℝ:=∑k∈Finset.Iic q,(k:ℝ)*‖coeff k A‖

theorem original (q:ℕ)(A:PowerSeries R)(z w:ℂ)(hz:‖z‖≤1)(hw:‖w‖≤1):
    ‖value (trunc (q+1) A) z-value (trunc (q+1) A) w‖≤ slope q A*‖z-w‖:=by
  rw [WilsonPositionScaleLawGuardEval.printed,WilsonPositionScaleLawGuardEval.printed,←Finset.sum_sub_distrib]
  calc
    _≤∑k∈Finset.Iic q,‖z^k • coeff k A-w^k • coeff k A‖:=norm_sum_le _ _
    _≤∑k∈Finset.Iic q,((k:ℝ)*‖coeff k A‖)*‖z-w‖:=by
      apply Finset.sum_le_sum;intro k _
      rw [←sub_smul,norm_smul]
      calc
        _≤((k:ℝ)*‖z-w‖)*‖coeff k A‖:=mul_le_mul_of_nonneg_right (power z w hz hw k) (norm_nonneg _)
        _=_:=by ring
    _=_:=by rw [slope,Finset.sum_mul]

end YM.Integration.WilsonPositionScaleLawGuardLipschitz
