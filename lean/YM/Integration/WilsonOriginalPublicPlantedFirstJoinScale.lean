import YM.Integration.WilsonOriginalPublicPlantedStableCredit

/-! Sum the actual fine-date scales at the first joining edge. All designated
slots retain their income even when another pair makes the first connection. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPlantedFirstJoinScale
open Finset Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank
open private tape from YM.Integration.WilsonOriginalPublicPlantedStableCredit
open scoped BigOperators Topology Classical

def radius (S:Schedule)(m d:ℕ):ℝ:=Real.exp (-(S.scale (m+d)-S.scale m))

theorem positive (S:Schedule)(m d:ℕ):0<radius S m d:=Real.exp_pos _

/-- The positive gain is measured on the actual optical mesh, including its
possibly longer finest block. The constant is uniform in the number of dates. -/
theorem pay (S:Schedule)(m N:ℕ)(δ:ℝ)(hp:0<δ)(a H:ℝ)(designated:ℕ)
    (clear:1≤a-H-(designated:ℝ)/4):
    ∑i ∈ range N,(radius S m i)^(a-H)*(δ/radius S m i)^((designated:ℝ)/4)
        ≤2*δ^((designated:ℝ)/4):=by
  let t:ℝ:=(designated:ℝ)/4
  let γ:=a-H-t
  have gain:1≤γ:=clear
  have sample (i:ℕ):(radius S m i)^(a-H)*(δ/radius S m i)^t
      =δ^t*Real.exp (-(S.scale (m+i)-S.scale m)*γ):=by
    rw [Real.rpow_def_of_pos (positive S m i),Real.rpow_def_of_pos (div_pos hp (positive S m i)),
      Real.rpow_def_of_pos hp,Real.log_div hp.ne' (positive S m i).ne']
    dsimp only [radius]
    simp only [Real.log_exp,←Real.exp_add]
    congr 1
    dsimp [γ]
    ring
  have fees (i:ℕ):Real.exp (-(S.scale (m+i)-S.scale m)*γ)≤((2:ℝ)⁻¹)^i:=by
    have charge:0≤S.scale (m+i)-S.scale m:=(mul_nonneg (Nat.cast_nonneg i)
      (Real.log_nonneg (by norm_num:1≤(3:ℝ)))).trans (tape S m i)
    have roof:(i:ℝ)*Real.log 2≤S.scale (m+i)-S.scale m:=
      (mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (by norm_num: (2:ℝ)≤3))
        (Nat.cast_nonneg i)).trans (tape S m i)
    rw [←Real.exp_log (pow_pos (by norm_num:(0:ℝ)<(2:ℝ)⁻¹) i),Real.log_pow,Real.log_inv]
    apply Real.exp_le_exp.mpr
    nlinarith only [roof,mul_le_mul_of_nonneg_left gain charge]
  have series:(∑i ∈ range N,((2:ℝ)⁻¹)^i)≤2:=by
    have h:=geom_sum_mul ((2:ℝ)⁻¹) N
    have g:0≤((2:ℝ)⁻¹)^N:=by positivity
    norm_num at h
    linarith
  change _≤2*δ^t
  calc
    _≤∑i ∈ range N,δ^t*((2:ℝ)⁻¹)^i:=Finset.sum_le_sum fun i _=>by
      rw [sample]
      exact mul_le_mul_of_nonneg_left (fees i) (Real.rpow_nonneg hp.le _)
    _=δ^t*∑i ∈ range N,((2:ℝ)⁻¹)^i:=by rw [Finset.mul_sum]
    _≤2*δ^t:=by simpa only [mul_comm _ (2:ℝ)] using
      mul_le_mul_of_nonneg_left series (Real.rpow_nonneg hp.le t)

/-- The real signed later scalar can keep the no-join contribution. Each
emitted join charge is on its entire product with the later normalized reader. -/
theorem signed {V:Type*}[SeminormedAddCommGroup V](S:Schedule)(m N:ℕ)(δ:ℝ)(hp:0<δ)
    (a H:ℝ)(n:ℕ)(clear:1≤a-H-(n:ℝ)/4)(A:ℝ)(cash:0≤A)(full noJoin:V)(join:ℕ→V)
    (file:full=noJoin+∑i ∈ range N,join i)
    (each:∀i<N,‖join i‖≤A*(radius S m i)^(a-H)*(δ/radius S m i)^((n:ℝ)/4)):
    ‖full-noJoin‖≤2*A*δ^((n:ℝ)/4):=by
  rw [file,add_sub_cancel_left]
  calc
    _≤∑i ∈ range N,‖join i‖:=norm_sum_le .. 
    _≤∑i ∈ range N,A*((radius S m i)^(a-H)*(δ/radius S m i)^((n:ℝ)/4)):=by
      exact sum_le_sum fun i hi=>by simpa only [mul_assoc] using each i (mem_range.mp hi)
    _=A*∑i ∈ range N,(radius S m i)^(a-H)*(δ/radius S m i)^((n:ℝ)/4):=by rw [mul_sum]
    _≤2*A*δ^((n:ℝ)/4):=by
      have h:=mul_le_mul_of_nonneg_left (pay S m N δ hp a H n clear) cash
      linarith

end YM.Integration.WilsonOriginalPublicPlantedFirstJoinScale
