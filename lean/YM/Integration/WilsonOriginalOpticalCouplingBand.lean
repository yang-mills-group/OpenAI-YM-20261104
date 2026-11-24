import YM.Integration.WilsonOriginalPhysicalCorridorLength

/-! Coupling and tariff conversion between actual dates in a polynomial Wilson mesh interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOpticalCouplingBand
open Function Filter Lattice Wilson RG
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure Pert.Asymptotics
open scoped Topology

variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "g" N:max per:max i:max => regulatorRun R.family N per i

private theorem ratios {x y:ℝ}(xp:0<x)(yp:0<y)(lo:y ≤ 4*x)(hi:x ≤ 9*y):
    (Real.sqrt x)⁻¹ ≤ 2*(Real.sqrt y)⁻¹ ∧ (Real.sqrt y)⁻¹ ≤ 3*(Real.sqrt x)⁻¹:=by
  have down:=Real.sqrt_le_sqrt lo
  have up:=Real.sqrt_le_sqrt hi
  rw [Real.sqrt_mul (by norm_num:0≤(4:ℝ)),show Real.sqrt 4=2 by norm_num] at down
  rw [Real.sqrt_mul (by norm_num:0≤(9:ℝ)),show Real.sqrt 9=3 by norm_num] at up
  constructor
  · simpa only [div_eq_mul_inv,one_mul] using ((div_le_div_iff₀ (Real.sqrt_pos.mpr xp) (Real.sqrt_pos.mpr yp)).mpr
      (show 1*Real.sqrt y ≤ 2*Real.sqrt x by simpa only [one_mul] using down))
  · simpa only [div_eq_mul_inv,one_mul] using ((div_le_div_iff₀ (Real.sqrt_pos.mpr yp) (Real.sqrt_pos.mpr xp)).mpr
      (show 1*Real.sqrt x ≤ 3*Real.sqrt y by simpa only [one_mul] using up))

include simple in
theorem scale (d:ℕ):∀ᶠ b:ℕ in atTop,∀{N per K i:ℕ},b ≤ i → i ≤ K → K ≤ N →
    R.family.S.a b/R.family.S.a K ≤ (H b)^d →
    (H b) ≤ H i ∧ (H i) ≤ 4*((g N per b)⁻¹)^2 ∧
    (g N per i) ≤ 2*(g N per b) ∧ (g N per b)⁻¹ ≤ 2*(g N per i)⁻¹ ∧ (g N per i)⁻¹ ≤ 3*(g N per b)⁻¹:=by
  let c:=G.slopeConstant*(d:ℝ)
  have cp:=Gauge.slopeConstant_pos simple
  have c0:0 ≤ c:=mul_nonneg cp.le (Nat.cast_nonneg _)
  filter_upwards [(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop ((2*c)^2)] with b base
  intro N per K i bi ik live re
  have hp:0<H b:=zero_lt_one.trans (R.family.path.levels.fits.delayed b)
  have sqp:=Real.sqrt_pos.mpr hp
  have small:2*c ≤ Real.sqrt (H b):=Real.le_sqrt_of_sq_le base
  have logb:Real.log (H b) ≤ 2*Real.sqrt (H b):=by
    calc Real.log (H b)=Real.log ((Real.sqrt (H b))^2):=by rw [Real.sq_sqrt hp.le]
         _ = 2*Real.log (Real.sqrt (H b)):=by rw [Real.log_pow];norm_num
         _ ≤ _:=by linarith only [Real.log_le_self sqp.le]
  have hd:c*Real.log (H b) ≤ H b:=by
    calc c*Real.log (H b) ≤ c*(2*Real.sqrt (H b)):=mul_le_mul_of_nonneg_left logb c0
         _ = (2*c)*Real.sqrt (H b):=by ring
         _ ≤ Real.sqrt (H b)*Real.sqrt (H b):=mul_le_mul_of_nonneg_right small sqp.le
         _ = H b:=Real.mul_self_sqrt hp.le
  have optical:=Real.log_le_log (div_pos (R.family.S.a_pos b) (R.family.S.a_pos K)) re
  rw [Real.log_pow,Real.log_div (R.family.S.a_pos b).ne' (R.family.S.a_pos K).ne'] at optical
  have span:R.family.S.scale K-R.family.S.scale b ≤ (d:ℝ)*Real.log (H b):=by
    simpa only [Schedule.scale,Real.log_inv,neg_sub_neg] using optical
  have diff:(H K)-(H b) ≤ c*Real.log (H b):=by
    calc (H K)-(H b)=G.slopeConstant*(R.family.S.scale K-R.family.S.scale b):=by
           change (_+G.slopeConstant*R.family.S.scale K)-(_+G.slopeConstant*R.family.S.scale b)=_
           ring
         _ ≤ G.slopeConstant*((d:ℝ)*Real.log (H b)):=mul_le_mul_of_nonneg_left span cp.le
         _ = _:=by dsimp only [c];ring
  have budget:(H K) ≤ 2*(H b):=by linarith only [diff,hd]
  have high:(H i) ≤ H K:=WilsonStartup.Timing.hat_mono R.family.path.levels cp.le ik
  have low:(H b) ≤ H i:=WilsonStartup.Timing.hat_mono R.family.path.levels cp.le bi
  let y:=R.family.path.β N per b
  let x:=R.family.path.β N per i
  have by0:(H b)/2 ≤ y ∧ y ≤ 2*(H b):=(R.makes.wilson.represents N per b (bi.trans (ik.trans live))).band
  have ix0:(H i)/2 ≤ x ∧ x ≤ 2*(H i):=(R.makes.wilson.represents N per i (ik.trans live)).band
  have yp:0<y:=by linarith only [by0.1,hp]
  have xp:0<x:=by linarith only [ix0.1,hp,low]
  have lo:y ≤ 4*x:=by linarith only [by0.2,ix0.1,low]
  have hi:x ≤ 9*y:=by linarith only [by0.1,ix0.2,high,budget,hp]
  have pair:=ratios xp yp lo hi
  refine ⟨low,?_,pair.1,?_,?_⟩
  · change (H i) ≤ 4*((Real.sqrt y)⁻¹)⁻¹^2
    rw [inv_inv,Real.sq_sqrt yp.le]
    linarith only [high,budget,by0.1]
  · change ((Real.sqrt y)⁻¹)⁻¹ ≤ 2*((Real.sqrt x)⁻¹)⁻¹
    rw [inv_inv,inv_inv]
    simpa only [Real.sqrt_mul (by norm_num:0≤(4:ℝ)),show Real.sqrt 4=2 by norm_num] using Real.sqrt_le_sqrt lo
  · change ((Real.sqrt x)⁻¹)⁻¹ ≤ 3*((Real.sqrt y)⁻¹)⁻¹
    rw [inv_inv,inv_inv]
    simpa only [Real.sqrt_mul (by norm_num:0≤(9:ℝ)),show Real.sqrt 9=3 by norm_num] using Real.sqrt_le_sqrt hi

include simple in
theorem cold (price:ℝ):∀ᶠ b:ℕ in atTop,∀(N per:ℕ),b ≤ N → price ≤ (g N per b)⁻¹:=by
  filter_upwards [(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (2*(max price 1)^2)] with b paid
  intro N per live
  have band:(H b)/2 ≤ R.family.path.β N per b:=(R.makes.wilson.represents N per b live).band.1
  change price ≤ ((Real.sqrt (R.family.path.β N per b))⁻¹)⁻¹
  rw [inv_inv]
  exact (le_max_left price 1).trans (Real.le_sqrt_of_sq_le (by linarith only [paid,band]))

end YM.Integration.WilsonOriginalOpticalCouplingBand
end
