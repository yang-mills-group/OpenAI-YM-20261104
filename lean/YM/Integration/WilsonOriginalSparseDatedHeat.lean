import YM.Integration.WilsonOriginalCensusChronologicalMoney
import YM.Integration.WilsonOriginalOpticalCouplingBand

/-! Two finite numerical thirds of a sparse face are paid by the true temperatures at adjacent dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseDatedHeat
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset Pressure Pert.Asymptotics
open scoped Topology

private theorem ratio {H β γ:ℝ} (hp:0<H)(left:H/2≤β)(right:γ≤4*H)(positive:0<γ):
    H⁻¹≤4*((Real.sqrt γ)⁻¹)^2 ∧ (Real.sqrt β)⁻¹≤3*(Real.sqrt γ)⁻¹:=by
  have bp:0<β:=by linarith only [hp,left]
  have id:γ*((Real.sqrt γ)⁻¹)^2=1:=by rw [inv_pow,Real.sq_sqrt positive.le,mul_inv_cancel₀ positive.ne']
  constructor
  · apply (inv_le_iff_one_le_mul₀ hp).mpr
    have z:=mul_le_mul_of_nonneg_right right (sq_nonneg (Real.sqrt γ)⁻¹)
    nlinarith only [id,z]
  · have h:γ≤9*β:=by linarith only [left,right,bp]
    have z:=Real.sqrt_le_sqrt h
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤9),show Real.sqrt 9=3 by norm_num] at z
    simpa only [div_eq_mul_inv,one_mul] using ((div_le_div_iff₀ (Real.sqrt_pos.mpr bp)
      (Real.sqrt_pos.mpr positive)).mpr (show 1*Real.sqrt γ≤3*Real.sqrt β by simpa only [one_mul] using z))

private theorem portion {f:ℝ}(positive:0<f)(small:f≤1)(P d:ℕ)(room:P+1≤d){M:ℝ}
    (pos:0≤M)(paid:3*M*f≤1):M*f^d≤f^P/3:=by
  have order:=pow_le_pow_of_le_one positive.le small room
  have h:=mul_le_mul_of_nonneg_left order pos
  rw [pow_succ] at h
  have w:=mul_le_mul_of_nonneg_right paid (pow_nonneg positive.le P)
  linarith only [h,w]

variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "g" N:max per:max i:max => regulatorRun R.family N per i

include simple in
theorem original (P power target:ℕ)(pw:P+1≤power)(out:P+1≤target)(M:ℝ)(mp:0≤M):
    ∀ᶠ i:ℕ in atTop,∀N per,i+1≤N →
      ((H i)^power)⁻¹≤(g N per (i+1))^P/3 ∧
        M*(g N per i)^target≤(g N per (i+1))^P/3:=by
  let cap:=3*((4:ℝ)^power+M*3^target)
  obtain ⟨start,purchase⟩:=eventually_atTop.mp (WilsonOriginalOpticalCouplingBand.cold R simple cap)
  filter_upwards [eventually_ge_atTop start,RG01.Physical.nextHat simple R.family.path.levels,
    WilsonOriginalCensusChronologicalMoney.thermal R simple] with i late hats thermal
  intro N per live
  let f:=g N per (i+1)
  let c:=g N per i
  have ib:i≤N:=by omega
  have fp:0<f:=(thermal (per:=per) (Nat.le_succ i) live).1
  have fs:f≤1:=by have := (thermal (per:=per) (Nat.le_succ i) live).2; linarith
  have cp:0<c:=(thermal (per:=per) le_rfl ib).1
  have hp:0<H i:=zero_lt_one.trans (R.family.path.levels.fits.delayed i)
  have hn:0<H (i+1):=zero_lt_one.trans (R.family.path.levels.fits.delayed (i+1))
  have left:(H i)/2≤R.family.path.β N per i:=(R.makes.wilson.represents N per i ib).band.1
  have sides:(H (i+1))/2≤R.family.path.β N per (i+1) ∧ R.family.path.β N per (i+1)≤2*(H (i+1)):=(R.makes.wilson.represents N per (i+1) live).band
  have γ:0<R.family.path.β N per (i+1):=by linarith only [hn,sides.1]
  have right:R.family.path.β N per (i+1)≤4*H i:=by linarith only [hats,sides.2,hp]
  have edges:(H i)⁻¹≤4*f^2 ∧ c≤3*f:=ratio hp left right γ
  have cash:cap*f≤1:=calc
    _≤f⁻¹*f:=mul_le_mul_of_nonneg_right (purchase (i+1) (by omega) N per live) fp.le
    _=1:=inv_mul_cancel₀ fp.ne'
  have pc:0≤M*3^target:=mul_nonneg mp (by positivity)
  have high:3*(4:ℝ)^power*f≤1:=by dsimp only [cap] at cash; nlinarith only [cash,mul_nonneg pc fp.le]
  have low:3*(M*3^target)*f≤1:=by
    dsimp only [cap] at cash
    nlinarith only [cash,mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤4) power) fp.le]
  constructor
  · calc
      _=((H i)⁻¹)^power:=(inv_pow _ _).symm
      _≤(4*f^2)^power:=pow_le_pow_left₀ (inv_nonneg.mpr hp.le) edges.1 _
      _=4^power*f^(2*power):=by rw [mul_pow,pow_mul]
      _≤f^P/3:=portion fp fs P (2*power) (by omega) (by positivity) high
  · calc
      _≤M*(3*f)^target:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ cp.le edges.2 _) mp
      _=(M*3^target)*f^target:=by rw [mul_pow,mul_assoc]
      _≤f^P/3:=portion fp fs P target out pc low

end YM.Integration.WilsonOriginalSparseDatedHeat
end
