import YM.Integration.WilsonThermometerMixedThermal
import YM.Integration.WilsonReportingForestMovingCount

/- Spend a single fine coupling power on every marker reduction through a fixed
   polylogarithmic number of original dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedCollarSubpower
open Filter Asymptotics Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato ActualRunKernelPackets FVA1 RG16.Literal Source Pressure ConnectedActivityE6
open Pert.Asymptotics
open scoped Classical Topology
def scale (x:ℝ):ℝ:=1+max 0 (Real.log (Real.log x))

private theorem budget (C:ℝ) (c0:0 ≤ C) (n:ℕ):
    ∀ᶠ h:ℝ in atTop,C*(1+max 0 (Real.log h))^n ≤ h/2:=by
  let K:=C*(2:ℝ)^n
  have k0:0 ≤ K:=mul_nonneg c0 (by positivity)
  have tiny:=(isLittleO_log_rpow_rpow_atTop (n:ℝ) (show (0:ℝ)<1 by norm_num)).def
    (show 0<(2*(K+1))⁻¹ by positivity)
  filter_upwards [tiny,eventually_ge_atTop (Real.exp 1)] with h small deep
  have h0:0<h:=(Real.exp_pos _).trans_le deep
  have log1:1 ≤ Real.log h:=by simpa only [Real.log_exp] using (Real.log_le_log (Real.exp_pos _) deep)
  have log0:0 ≤ Real.log h:=zero_le_one.trans log1
  have fit:(Real.log h)^n ≤ (2*(K+1))⁻¹*h:=by
    change ‖(Real.log h)^(n:ℝ)‖ ≤ (2*(K+1))⁻¹*‖h^(1:ℝ)‖ at small
    simpa only [Real.rpow_natCast,Real.rpow_one,Real.norm_of_nonneg (pow_nonneg log0 _),Real.norm_of_nonneg h0.le] using small
  have factor:K*(2*(K+1))⁻¹ ≤ (2:ℝ)⁻¹:=by
    rw [←div_eq_mul_inv]
    exact (div_le_iff₀ (by positivity)).2 (by linarith only [k0])
  rw [max_eq_right log0]
  calc
    C*(1+Real.log h)^n ≤ C*(2*Real.log h)^n := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [log0]) (by linarith only [log1]) n) c0
    _ = K*(Real.log h)^n:=by rw [mul_pow];dsimp only [K];ring
    _ ≤ K*((2*(K+1))⁻¹*h):=mul_le_mul_of_nonneg_left fit k0
    _ = (K*(2*(K+1))⁻¹)*h:=by ring
    _ ≤ (2:ℝ)⁻¹*h:=mul_le_mul_of_nonneg_right factor h0.le
    _ = h/2:=by ring

variable {G:Gauge} (R:Run G)(simple:G.Simple)
local notation "H" j:max => R.alloy.B.a.clock.hatBeta j

include simple in
theorem original (C:ℝ)(c0:0 ≤ C)(d:ℕ):
    ∀ᶠ f:ℕ in atTop,∀N,f+1≤N→∀per n,(n:ℝ) ≤ C*(scale (H (f+1)))^d →
    regulatorRun R.family N per (f+1)*Real.exp (3*n*(scale (H (f+1)))^3) ≤ 1:=by
  have grown:= (Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)
  have logs:=Real.tendsto_log_atTop.comp grown
  have small:=logs.eventually (budget (6*C) (by positivity) (d+3))
  filter_upwards [small,grown.eventually_ge_atTop (4:ℝ)] with f paid four N live per n span
  let g:=regulatorRun R.family N per (f+1)
  let h:=H (f+1)
  let z:=scale h
  let x:ℝ:=3*n*z^3
  change 4≤h at four
  have hp:0<h:=by linarith only [four]
  have z0:0≤z:=by dsimp [z,scale];linarith only [le_max_left 0 (Real.log (Real.log h))]
  change (6*C)*z^(d+3) ≤ (Real.log h)/2 at paid
  have doubled:2*x ≤ Real.log h/2:=by
    calc
      2*x=(6:ℝ)*(n:ℝ)*z^3:=by dsimp [x];ring
      _ ≤ (6*(C*z^d))*z^3:=by gcongr
      _ = (6*C)*z^(d+3):=by rw [pow_add];ring
      _ ≤ _:=paid
  have log2:2*Real.log 2 ≤ Real.log h:=by
    calc
      2*Real.log 2=Real.log ((2:ℝ)*2):=by rw [Real.log_mul (by norm_num) (by norm_num)];ring
      _ ≤ _:=Real.log_le_log (by norm_num) (by linarith only [four])
  have cap:=Real.exp_le_exp.mpr (show x+x+Real.log 2 ≤ Real.log h by linarith only [doubled,log2])
  rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num),Real.exp_log hp] at cap
  obtain ⟨gp,_,_,sq,_⟩:=WilsonThermometerMixedThermal.heat R simple (N:=N) (per:=per) live
  change g^2*h ≤ 2 at sq
  have combined:=mul_le_mul_of_nonneg_left cap (sq_nonneg g)
  have result:g^2*Real.exp x^2 ≤ 1:=by nlinarith only [combined,sq]
  change g*Real.exp x ≤ 1
  apply (sq_le_sq₀ (mul_nonneg gp.le (Real.exp_pos _).le) zero_le_one).1
  simpa only [mul_pow,one_pow] using result
end YM.Integration.WilsonThermometerMixedCollarSubpower
end
