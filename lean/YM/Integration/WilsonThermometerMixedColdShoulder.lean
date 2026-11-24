import YM.Integration.WilsonJointAxialClock
import YM.Integration.WilsonOriginalThermometerTollBudget
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedColdShoulder
open Filter Lattice Wilson RG Source Marker QuadraticLocal PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ActualRunKernelPackets Pressure Push.PriceCompiler ConnectedActivityE6 Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family
local notation "Y" n:max => R.family.path.levels.clock.hatBeta n

private theorem collar {x:ℝ}{D:ℕ}(d q:ℕ)(xp:0 < x)(size:(Real.log x)^2 ≤ (D:ℝ))
    (late:16*((d:ℝ)+(q:ℝ)+1) ≤ Real.log x):
    Real.exp (-(D/8:ℕ):ℝ)*x^d ≤ (x^q)⁻¹:=by
  have geo: D ≤ 8*(D/8)+7:=by omega
  have geo': (D:ℝ) ≤ 8*((D/8:ℕ):ℝ)+7:=by exact_mod_cast geo
  have ld:0 ≤ Real.log x:=by linarith only [late,Nat.cast_nonneg (α:=ℝ) d,Nat.cast_nonneg (α:=ℝ) q]
  have hc:=mul_le_mul_of_nonneg_right late ld
  have nn:=mul_nonneg (add_nonneg (Nat.cast_nonneg (α:=ℝ) d) (Nat.cast_nonneg (α:=ℝ) q)) ld
  have term:((d+q:ℕ):ℝ)*Real.log x ≤ (D/8:ℕ):=by
    push_cast
    nlinarith only [size,geo',hc,late,nn,Nat.cast_nonneg (α:=ℝ) d,Nat.cast_nonneg (α:=ℝ) q]
  rw [←one_div]
  apply (le_div_iff₀ (pow_pos xp _)).mpr
  calc
    _ = Real.exp (-(D/8:ℕ):ℝ)*x^(d+q):=by rw [pow_add];ring
    _ = Real.exp (-((D/8:ℕ):ℝ)+((d+q:ℕ):ℝ)*Real.log x):=by
      rw [Real.exp_add,←Real.log_pow,Real.exp_log (pow_pos xp _)]
    _ ≤ 1:=Real.exp_le_one_iff.mpr (by linarith only [term])

include simple in
/-- The genuine separation shoulder at the coarsened physical support pays the whole
old-mixed enlargement, at any prescribed fixed grade. Onset is before the regulators. -/
theorem original (d a q:ℕ):∀ᶠ i:ℕ in atTop,∀ N per:ℕ,i < N → ∀ E:ℝ,E ≤ (Y i)^d →
    let g:=regulatorRun R.family N per (i+1)
    (g^a)⁻¹*(Real.exp (-((((C).path.levels.budget i).B/8:ℕ):ℝ))*E) ≤ g^q:=by
  have grows:=Next.Rank.Station.hat_rate R.family.path.levels simple
  have logs:=Real.tendsto_log_atTop.comp grows
  filter_upwards [grows.eventually_ge_atTop 4,RG01.Physical.nextHat simple (C).path.levels,
    logs.eventually_ge_atTop (16*((d:ℝ)+((q+a:ℕ):ℝ)+1))] with i hot changeSize late N per live E price
  let g:=regulatorRun R.family N per (i+1)
  let β:=(C).path.rep N per (i+1) |>.beta
  let x:=Y i
  have xp:0 < x:=by exact zero_lt_one.trans ((C).path.levels.fits.delayed i)
  have gp:0 < g:=regulator_pos R N per (i+1) (by omega)
  have actual:=R.makes.wilson.represents N per (i+1) (by omega)
  have upper:β ≤ 2*(Y (i+1)):=by exact actual.band.2
  have grow: Y (i+1) ≤ 2*x:=changeSize
  have fat:4 ≤ x:=hot
  have cap:β ≤ x^2:=by nlinarith only [grow,upper,mul_nonneg (show 0 ≤ x-4 by linarith only [fat]) xp.le]
  have tip:0 < Real.sqrt β:=inv_pos.mp gp
  have r:Real.sqrt β ≤ x:= (Real.sqrt_le_iff).mpr ⟨xp.le,cap⟩
  have inv:(x:ℝ)⁻¹ ≤ g:=(inv_le_inv₀ xp tip).mpr r
  have off:=collar (D:=((C).path.levels.budget i).B) d (q+a) xp (Nat.le_ceil _) late
  have e:Real.exp ( -((((C).path.levels.budget i).B/8:ℕ):ℝ))*E ≤ g^(q+a):=
    (mul_le_mul_of_nonneg_left price (Real.exp_nonneg _)).trans
      (off.trans ((inv_pow ..).symm.le.trans (pow_le_pow_left₀ (inv_nonneg.mpr xp.le) inv _)))
  exact (mul_le_mul_of_nonneg_left e (inv_nonneg.mpr (pow_nonneg gp.le _))).trans_eq
    (by rw [pow_add];field_simp; rfl)

end YM.Integration.WilsonThermometerMixedColdShoulder
