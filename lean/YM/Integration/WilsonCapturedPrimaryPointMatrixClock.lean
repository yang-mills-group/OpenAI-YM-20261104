import YM.Integration.WilsonCapturedPrimaryPointInverse
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonCapturedPrimaryPointMatrixClock
open Filter Lattice RG Wilson WilsonPhysicalMarkedDefect Pert.Asymptotics
open PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
theorem band {N per i:ℕ}(hi:i≤N):
    R.family.path.levels.clock.hatBeta i*(regulatorRun R.family N per i)^2≤2:=by
  let b:=R.family.path.β N per i
  let g:=regulatorRun R.family N per i
  have bp:0<b:=Overlay.beta_positive R.makes.wilson hi
  have low:R.family.path.levels.clock.hatBeta i/2≤b:=(R.makes.wilson.represents N per i hi).band.1
  have same:b*g^2=1:=by
    change b*((Real.sqrt b)⁻¹)^2=1
    rw [inv_pow,Real.sq_sqrt bp.le,mul_inv_cancel₀ bp.ne']
  have upper:R.family.path.levels.clock.hatBeta i≤2*b:=by linarith
  exact (mul_le_mul_of_nonneg_right upper (sq_nonneg g)).trans_eq (by linarith only [same])

theorem original (simple:G.Simple){C M:ℝ}(pos:0<C)(mn:0≤M):
    ∀ᶠi:ℕ in atTop,∀N per:ℕ,i≤N→
      let g:=regulatorRun R.family N per i
      let H:=R.family.path.levels.clock.hatBeta i
      ∀q:ℕ,C*g^((q+3)+1)*(H^((1:ℝ)/8))*(1+H^((1:ℝ)/4)*M)≤g^(q+1):=by
  let cost:=2*C*(1+M)
  have cp:0<cost:=by dsimp [cost];positivity
  filter_upwards [WilsonCapturedPrimaryPointInverse.tiny R simple (b:=1/cost) (by positivity),
    (Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (1:ℝ)] with i paid warm
  intro N per hi g H q
  obtain ⟨gp,gr⟩:=paid N per hi
  have hn:0<H:=lt_of_lt_of_le zero_lt_one warm
  have e₁:H^((1:ℝ)/8)≤H:=by
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le warm (by norm_num:(1:ℝ)/8≤1))
  have e₂:H^((1:ℝ)/8)*H^((1:ℝ)/4)≤H:=by
    rw [←Real.rpow_add hn]
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le warm (by norm_num:(1:ℝ)/8+1/4≤1))
  have total:H^((1:ℝ)/8)*(1+H^((1:ℝ)/4)*M)≤(1+M)*H:=by
    linarith only [e₁,mul_le_mul_of_nonneg_right e₂ mn]
  have rent:g*cost≤1:=(le_div_iff₀ cp).mp gr
  have Hpaid:=band R (per:=per) hi
  have hcost:g*(2*C*(1+M))≤1:=rent
  have geom:H*g^2≤2:=Hpaid
  calc
    _ = (C*g^((q+3)+1))*(H^((1:ℝ)/8)*(1+H^((1:ℝ)/4)*M)):=by ring
    _ ≤ (C*g^((q+3)+1))*((1+M)*H):=
      mul_le_mul_of_nonneg_left total (mul_nonneg pos.le (pow_nonneg gp.le _))
    _ = (g^(q+1)*g*C*(1+M))*(H*g^2):=by ring
    _ ≤ (g^(q+1)*g*C*(1+M))*2:=mul_le_mul_of_nonneg_left geom (by change 0≤(regulatorRun R.family N per i)^_*_*_*_;positivity)
    _ = g^(q+1)*(g*(2*C*(1+M))):=by ring
    _ ≤ g^(q+1) := (mul_le_mul_of_nonneg_left hcost (pow_nonneg gp.le _)).trans_eq (mul_one _)

end YM.Integration.WilsonCapturedPrimaryPointMatrixClock
