import YM.Integration.WilsonOriginalAlternativeTrialCollateral

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialSeparationRate
open Filter WilsonThermometerMixedCollarSubpower
open scoped Topology
open private YM.Integration.WilsonThermometerMixedCollarSubpower.budget from YM.Integration.WilsonThermometerMixedCollarSubpower

theorem original (n a p:ℕ)(C e:ℝ)(c0:0≤C)(ep:0<e):
    ∀ᶠ H:ℝ in atTop,∀l B:ℕ,(l:ℝ)≤C*(1+Real.log H)→(Real.log H)^2≤(B:ℝ)→
      H^a*Real.exp ((n:ℝ)*(l:ℝ)*(scale H)^3)*Real.exp (-(2:ℝ)*((B/8:ℕ):ℝ))≤e*(H⁻¹)^p:=by
  have fare:=Real.tendsto_log_atTop.eventually (YM.Integration.WilsonThermometerMixedCollarSubpower.budget
    (32*(n:ℝ)*C) (by positivity) 3)
  have enough:=Real.tendsto_log_atTop.eventually_ge_atTop (16*((a:ℝ)+(p:ℝ)+2))
  filter_upwards [fare,enough,eventually_ge_atTop (1:ℝ),eventually_ge_atTop e⁻¹] with H hz raised h1 cash l B length area
  let t:=Real.log H
  let z:=scale H
  have hp:0<H:=zero_lt_one.trans_le h1
  have z0:0≤z:=by dsimp [z,scale];linarith only [le_max_left 0 (Real.log (Real.log H))]
  have t0:0≤t:=Real.log_nonneg h1
  change (32*(n:ℝ)*C)*z^3≤t/2 at hz
  change 16*((a:ℝ)+(p:ℝ)+2)≤t at raised
  have t1:1≤t:=by linarith only [raised,(Nat.cast_nonneg a:0≤(a:ℝ)),(Nat.cast_nonneg p:0≤(p:ℝ))]
  have inner:(n:ℝ)*C*z^3≤t/64:=by linarith only [hz]
  have long:(n:ℝ)*(l:ℝ)*z^3≤t^2/32:=by
    calc
      (n:ℝ)*(l:ℝ)*z^3≤(n:ℝ)*(C*(1+t))*z^3:=by gcongr
      _ = (1+t)*((n:ℝ)*C*z^3):=by ring
      _ ≤ (2*t)*(t/64):=mul_le_mul (by linarith only [t1]) inner (by positivity) (by positivity)
      _ = t^2/32:=by ring
  have rate:(a+p+1:ℝ)*t≤t^2/16:=by
    have h:(a+p+1:ℝ)≤t/16:=by linarith only [raised]
    nlinarith only [mul_le_mul_of_nonneg_right h t0]
  have b8:(B:ℝ)≤8*((B/8:ℕ):ℝ)+7:=by exact_mod_cast (by omega:B≤8*(B/8)+7)
  have base:16≤t:=by linarith only [raised,(Nat.cast_nonneg a:0≤(a:ℝ)),(Nat.cast_nonneg p:0≤(p:ℝ))]
  have t2:16≤t^2:=by nlinarith only [sq_nonneg (t-4),base]
  change t^2≤(B:ℝ) at area
  have loss:(a:ℝ)*t+((n:ℝ)*l*z^3)+(-(2:ℝ)*((B/8:ℕ):ℝ))≤-((p:ℝ)+1)*t:=by
    nlinarith only [long,rate,b8,area,t2]
  have started:H^a=Real.exp ((a:ℝ)*t):=by rw [Real.exp_nat_mul,Real.exp_log hp]
  have finish:Real.exp (-((p:ℝ)+1)*t)=(H⁻¹)^p*H⁻¹:=by
    rw [show -((p:ℝ)+1)*t=(p:ℝ)*(-t)+(-t) by ring,Real.exp_add,Real.exp_nat_mul,Real.exp_neg,Real.exp_log hp]
  have small:H⁻¹≤e:=by
    calc H⁻¹≤(e⁻¹)⁻¹:=(inv_le_inv₀ hp (inv_pos.2 ep)).2 cash
         _=e:=inv_inv _
  rw [started,←Real.exp_add,←Real.exp_add]
  calc
    _ ≤ Real.exp (-((p:ℝ)+1)*t):=Real.exp_le_exp.mpr loss
    _ = (H⁻¹)^p*H⁻¹:=finish
    _ ≤ (H⁻¹)^p*e:=mul_le_mul_of_nonneg_left small (pow_nonneg (inv_nonneg.2 hp.le) p)
    _ = e*(H⁻¹)^p:=mul_comm _ _

end YM.Integration.WilsonOriginalAlternativeTrialSeparationRate
end
