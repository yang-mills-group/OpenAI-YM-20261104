import YM.FullVolume.Cross
import Mathlib.Analysis.SpecificLimits.Normed

/-! Every fixed polynomial in the genuine stage index fits the original physical
torus, uniformly in the period, after one scale threshold. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedGeometryNonwrap
open Function Filter Lattice PhysicalNext.Repeat.Legato
open scoped Topology

theorem exponential (S : Schedule) (m : ℕ) : 3^m≤(S.denominator m).val := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ,Schedule.denominator,PNat.mul_coe]
    exact Nat.mul_le_mul ih (S.block_large m)

theorem side (S : Schedule) (m p : ℕ) : 3^m≤(S.side m p).val := by
  apply (exponential S m).trans
  change (S.denominator m).val≤(S.period p).val*(S.denominator m).val
  simpa only [one_mul] using Nat.mul_le_mul_right (S.denominator m).val
    (show 1≤(S.period p).val from (S.period p).property)

variable {G : Gauge} (R : Run G)
local notation "J" => R.family.path.levels.clock.J

theorem stages (m : ℕ) : J m≤J 0+m := by
  induction m with
  | zero => omega
  | succ m ih =>
    have h:=R.family.path.levels.fits.stepSlow m
    omega

theorem polynomial (K b r : ℕ) : ∀ᶠ m : ℕ in atTop, ∀p,
    K*(J (m+1)+b)^r<(R.family.side m p).val := by
  have base := tendsto_pow_const_div_const_pow_of_one_lt r (by norm_num : 1<(3:ℝ))
  have small : Tendsto (fun m : ℕ=>((K:ℝ)*2^r)*((m:ℝ)^r/(3:ℝ)^m)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul base
  filter_upwards [small.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    eventually_ge_atTop (J 0+b+1)] with m hlarge hm
  intro p
  have grow : K*2^r*m^r<3^m := by
    have h : ((K:ℝ)*2^r)*(m:ℝ)^r<(3:ℝ)^m := by
      apply (div_lt_one (pow_pos (by norm_num : (0:ℝ)<3) m)).mp
      simpa only [mul_div_assoc] using hlarge
    exact_mod_cast h
  have orders : J (m+1)+b≤2*m := by have h:=stages R (m+1); omega
  calc
    K*(J (m+1)+b)^r≤K*(2*m)^r := Nat.mul_le_mul_left K (Nat.pow_le_pow_left orders r)
    _ = K*2^r*m^r := by rw [mul_pow,mul_assoc]
    _ < 3^m := grow
    _ ≤ (R.family.side m p).val := side R.family.S m p

theorem block (K b r : ℕ) : ∀ᶠ m : ℕ in atTop, ∀p,
    K*(J (m+1)+b)^r*(R.family.S.block m).val<(R.family.side (m+1) p).val := by
  filter_upwards [polynomial R K b r] with m h
  intro p
  have exactSide : (R.family.side (m+1) p).val=(R.family.side m p).val*(R.family.S.block m).val := by
    change (R.family.S.period p).val*((R.family.S.denominator m).val*(R.family.S.block m).val)=_
    exact (Nat.mul_assoc ..).symm
  rw [exactSide]
  exact Nat.mul_lt_mul_of_pos_right (h p) (R.family.S.block m).property

end YM.Integration.WilsonLimitConstruction.FundedGeometryNonwrap
end
