import YM.Integration.WilsonMeasuredRankedPrimaryBudget
import YM.Integration.WilsonMeasuredRankedFare
import YM.Integration.WilsonReportHarvestUpperAge

/-! Combining the true ranked and full-group prices before restoring the source radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerFare

def unitCost (c K ω:ℝ) (q:ℕ) : ℝ :=
  (1+ω)*(2*c+2*Real.exp 102*(2:ℝ)^q+4*K)

theorem paid {w b x E c K H ω g:ℝ} (q:ℕ)
    (gp:0<g) (cool:g≤1) (cp:0≤c) (hp:0≤H) (kp:0≤K) (wrap:0≤ω)
    (clock:H*g^2≤2) (earned:E≤2*g^(q+4))
    (hard:w*b≤c*(g⁻¹)^4*E+2*Real.exp 102*(2*g^2)^q)
    (regular:w*x≤(1+ω)*(K*H)*E+ω*(w*b)) :
    w*(b+x)≤unitCost c K ω q*g^q := by
  have back:(g⁻¹)^4*g^(q+4)=g^q:=by
    rw [pow_add]
    field_simp
  have small:g^2≤g:=by rw [sq];simpa using mul_le_mul_of_nonneg_left cool gp.le
  have small₁:g^2≤1:=small.trans cool
  have geometric:(2*g^2)^q≤(2:ℝ)^q*g^q:=by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) small _) (by positivity)
  have z:c*(g⁻¹)^4*E≤2*c*g^q:=calc
    _ ≤ c*(g⁻¹)^4*(2*g^(q+4)):=mul_le_mul_of_nonneg_left earned (by positivity)
    _ = 2*c*((g⁻¹)^4*g^(q+4)):=by ring
    _ = _:=by rw [back]
  have row:w*b≤(2*c+2*Real.exp 102*(2:ℝ)^q)*g^q:=calc
    _ ≤ _:=hard
    _ ≤ 2*c*g^q+2*Real.exp 102*((2:ℝ)^q*g^q):=add_le_add z (mul_le_mul_of_nonneg_left geometric (by positivity))
    _ = _:=by ring
  have he:H*E≤4*g^q:=calc
    _ ≤ H*(2*g^(q+4)):=mul_le_mul_of_nonneg_left earned hp
    _ = (H*g^2)*(2*g^2*g^q):=by rw [pow_add];ring
    _ ≤ 2*(2*1*g^q):=by gcongr
    _ = _:=by ring
  calc
    _ = w*b+w*x:=by ring
    _ ≤ w*b+((1+ω)*(K*H)*E+ω*(w*b)):=by gcongr
    _ = (1+ω)*(w*b+K*(H*E)):=by ring
    _ ≤ (1+ω)*((2*c+2*Real.exp 102*(2:ℝ)^q)*g^q+K*(4*g^q)):=by gcongr
    _ = _:=by unfold unitCost;ring

theorem scaled {L g C B t:ℝ} (q d:ℕ) (bp:0<B) (lp:0≤L) (gp:0<g) (cp:0≤C)
    (stage:L*g^2≤2) (paid:(2*B)⁻¹*t≤C*g^(q+2*d)) :
    L^d*t≤(2*B)*((2:ℝ)^d*C)*g^q := by
  have raw:t≤(2*B)*(C*g^(q+2*d)):=by
    calc
      _ = (2*B)*((2*B)⁻¹*t):=by field_simp
      _ ≤ _:=mul_le_mul_of_nonneg_left paid (by positivity)
  have clock:(L*g^2)^d≤(2:ℝ)^d:=pow_le_pow_left₀ (mul_nonneg lp (sq_nonneg _)) stage d
  calc
    _ ≤ L^d*((2*B)*(C*g^(q+2*d))):=mul_le_mul_of_nonneg_left raw (pow_nonneg lp _)
    _ = ((2*B)*C*g^q)*(L*g^2)^d:=by rw [pow_add,mul_pow,pow_mul];ring
    _ ≤ ((2*B)*C*g^q)*2^d:=mul_le_mul_of_nonneg_left clock (by positivity)
    _ = _:=by ring

end YM.Integration.WilsonMeasuredOwnerFare
