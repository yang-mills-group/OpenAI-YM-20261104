import YM.Integration.WilsonVacuumPreResetCurvatureTariff
import YM.Integration.WilsonVacuumPreResetRenderIncome

/-! Coupling powers for the full signed curvature tariff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCurvatureCharge
open Filter RG Lattice
open scoped Topology

def factor (η:ℝ):ℝ:=(2:ℝ)^(η/2)/(η/2)

theorem logarithm {η b g:ℝ}(ep:0<η)(bp:0<b)(gp:0<g)(band:b≤2*(g^2)⁻¹):
    Real.log b≤factor η*g^(-η):=by
  let r:=η/2
  have rp:0<r:=by dsimp [r];positivity
  have l:r*Real.log b≤b^r:=by
    rw [←Real.log_rpow bp]
    linarith [Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos bp r)]
  have y:=Real.rpow_le_rpow bp.le band rp.le
  have f:(2*(g^2)⁻¹)^r=(2:ℝ)^r*g^(-η):=by
    rw [Real.mul_rpow (by norm_num) (by positivity),Real.inv_rpow (sq_nonneg _),
      ←Real.rpow_neg (sq_nonneg _),←Real.rpow_natCast_mul gp.le]
    congr 2
    dsimp [r];ring
  unfold factor
  calc
    Real.log b ≤ ((2:ℝ)^r*g^(-η))/r := (le_div_iff₀ rp).mpr (by rw [mul_comm];exact l.trans (y.trans_eq f))
    _ = _ := by dsimp [r];ring

theorem physical {g A θ T α M:ℝ}(gp:0<g)(small:g≤1)(big:1≤A)(hp:0<θ)(ht:θ≤1)
    (room:θ≤2*g*A)(mp:0≤M)(tail:|T|≤M*A)(base:|α|≤A):
    |g^2*T| * θ^2+|g^2*T+α| * θ^3+|g^2*T+α| * θ^4≤20*(M+1)*g^3*A^4:=by
  have ap:0≤A:=zero_le_one.trans big
  have u:|g^2*T| ≤g^2*(M*A):=by rw [abs_mul,abs_of_nonneg (sq_nonneg _)];gcongr
  have uu:|g^2*T| ≤ M*A:=
    u.trans (mul_le_of_le_one_left (mul_nonneg mp ap) (pow_le_one₀ gp.le small))
  have v:|g^2*T+α|≤(M+1)*A:=(abs_add_le ..).trans (by linarith [add_le_add uu base])
  have l:|g^2*T| *θ^2≤4*(M+1)*g^3*A^4:=by
    calc
      _≤(g^2*(M*A))*(2*g*A)^2:=by gcongr
      _=4*M*g^4*A^3:=by ring
      _≤4*(M+1)*g^3*A^4:=by
        have ge:g^4≤g^3:=pow_le_pow_of_le_one gp.le small (by decide)
        have ae:A^3≤A^4:=pow_le_pow_right₀ big (by decide)
        have me:M≤M+1:=by linarith
        exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left me (by norm_num)) ge
          (by positivity) (by positivity)) ae (by positivity) (by positivity)
  have hi:|g^2*T+α| *θ^3≤8*(M+1)*g^3*A^4:=by
    calc
      _≤((M+1)*A)*(2*g*A)^3:=by gcongr
      _= _:=by ring
  have four:|g^2*T+α| *θ^4≤8*(M+1)*g^3*A^4:=
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hp.le ht (by norm_num)) (abs_nonneg _)).trans hi
  linarith only [l,hi,four]

theorem gain {g:ℝ}(gp:0<g):
    g^3*(g^(-(1/20:ℝ)))^5=g^(11/4:ℝ):=by
  rw [←Real.rpow_natCast g 3,←Real.rpow_mul_natCast gp.le,←Real.rpow_add gp]
  norm_num

end YM.Integration.WilsonVacuumPreResetCurvatureCharge
