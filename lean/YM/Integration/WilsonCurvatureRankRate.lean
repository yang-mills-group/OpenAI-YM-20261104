import YM.Integration.WilsonThermalPacketSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The uniform loss from the true transported-curvature endpoints on the
original thermal clock. No estimate on the walk length is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCurvatureRankRate
open Filter Finset Lattice Wilson RG OPE.Therm Next.Rank
open WilsonThermalPacketSum
open scoped Classical BigOperators Topology
variable {G : Gauge}

theorem cap (c r m : ℕ) {t δ budget a : ℝ} (hB : 0 ≤ budget) (ha : 0 ≤ a)
    (hA : ∀ q ∈ Finset.Icc c r, t^q + 2^q*((q:ℝ)*δ) ≤ a) :
    cost c r m t δ budget ≤ ((r+1:ℕ):ℝ)*(m:ℝ)*(a*budget) := by
  have hcard : (Finset.Icc c r).card ≤ r+1 := by
    have h : Finset.Icc c r ⊆ Finset.range (r+1) :=
      fun q hq => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hq).2)
    simpa only [Finset.card_range] using Finset.card_le_card h
  calc
    _ ≤ ∑ _q ∈ Finset.Icc c r,(m:ℝ)*(a*budget) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hA q hq) hB) (Nat.cast_nonneg _)
    _ = ((Finset.Icc c r).card:ℝ)*((m:ℝ)*(a*budget)) := by simp
    _ ≤ ((r+1:ℕ):ℝ)*((m:ℝ)*(a*budget)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ha hB))
    _ = _ := by ring

theorem at_two (c r m : ℕ) {budget : ℝ} (hb : 0 ≤ budget) :
    cost c r m 2 0 budget ≤ ((r+1:ℕ):ℝ)*(m:ℝ)*((2:ℝ)^r*budget) := by
  apply cap c r m hb (by positivity)
  intro q h
  simpa only [mul_zero,add_zero] using
    (pow_le_pow_right₀ (show 1 ≤ (2:ℝ) by norm_num) (Finset.mem_Icc.mp h).2)

theorem thermal (A : Levels G) (hG : G.Simple) (c : ℕ) {s : ℝ} (hs : s < c) :
    ∀ᶠ i : ℕ in atTop, 0 ≤ cool A i ∧
      (cool A i)^c ≤ (A.clock.hatCoupling i)^s ∧
      vanishP A i ≤ (A.clock.hatCoupling i)^s := by
  have hx := Station.hat_rate A hG
  have hε : 0 < ((c:ℝ)-s)/2 := half_pos (sub_pos.mpr hs)
  have hp := (isLittleO_log_rpow_rpow_atTop ((12*c:ℕ):ℝ) hε).def (c:=1) zero_lt_one
  filter_upwards [hx.eventually hp,(Real.tendsto_log_atTop.comp hx).eventually_ge_atTop (max 0 (s/2))] with i hi hlog
  let b := A.clock.hatBeta i
  let g := A.clock.hatCoupling i
  have hb : 0 < b := zero_lt_one.trans (A.fits.delayed i)
  have hL : 0 ≤ Real.log b := (le_max_left _ _).trans hlog
  have hLs : s/2 ≤ Real.log b := (le_max_right _ _).trans hlog
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr hb)
  have idg (y : ℝ) : g^y = b^(-y/2) := by
    change ((Real.sqrt b)⁻¹)^y = _
    rw [← Real.rpow_neg_one,Real.sqrt_eq_rpow,← Real.rpow_mul hb.le,← Real.rpow_mul hb.le]
    congr 1
    ring
  have hl : (Real.log b)^(12*c) ≤ g^(s-c) := by
    rw [idg]
    have eqn : -(s - (c:ℝ))/2=((c:ℝ)-s)/2 := by ring
    rw [eqn]
    change ‖(Real.log b)^((12*c:ℕ):ℝ)‖ ≤ 1*‖b^(((c:ℝ)-s)/2)‖ at hi
    simpa only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg hL (12*c)),
      Real.norm_of_nonneg (Real.rpow_nonneg hb.le _),one_mul] using hi
  refine ⟨mul_nonneg hg.le (pow_nonneg hL 12),?_,?_⟩
  · calc
      _ = g^(c:ℝ)*(Real.log b)^(12*c) := by
        simp only [cool,sigmaU,g,b,mul_pow,pow_mul,Real.rpow_natCast]
      _ ≤ g^(c:ℝ)*g^(s-c) := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hg.le _)
      _ = _ := by rw [←Real.rpow_add hg]; congr 1; ring
  · change Real.exp (-(Real.log b)^2) ≤ g^s
    rw [idg,Real.rpow_def_of_pos hb]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hL (sub_nonneg.mpr hLs)]

theorem funded (A : Levels G) (hG : G.Simple) (c r m : ℕ) {s : ℝ} (hs : s < c) :
    ∀ᶠ i : ℕ in atTop, ∀ budget : ℝ, 0 ≤ budget →
      cost c r m (cool A i) (vanishP A i) budget ≤
        ((r+1:ℕ):ℝ)*(m:ℝ)*(((1+2^r*(r:ℝ))*(A.clock.hatCoupling i)^s)*budget) := by
  filter_upwards [thermal A hG c hs,thermal A hG 1 (s:=0) (by norm_num)] with i h h1
  intro budget hB
  have ht : cool A i ≤ 1 := by simpa only [pow_one,Real.rpow_zero] using h1.2.1
  have hg : 0 < A.clock.hatCoupling i := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (A.fits.delayed i)))
  have hc := Real.rpow_nonneg hg.le s
  have hv : 0 ≤ vanishP A i := (Real.exp_pos _).le
  apply cap c r m hB (by positivity)
  intro q hq
  have hqr := (Finset.mem_Icc.mp hq).2
  have hlow := (pow_le_pow_of_le_one h.1 ht (Finset.mem_Icc.mp hq).1).trans h.2.1
  have h2 := pow_le_pow_right₀ (show 1 ≤ (2:ℝ) by norm_num) hqr
  have hqv : (q:ℝ)*vanishP A i ≤ (r:ℝ)*(A.clock.hatCoupling i)^s :=
    mul_le_mul (by exact_mod_cast hqr) h.2.2 hv (Nat.cast_nonneg _)
  calc
    _ ≤ (A.clock.hatCoupling i)^s + 2^r*((r:ℝ)*(A.clock.hatCoupling i)^s) :=
      add_le_add hlow (mul_le_mul h2 hqv (mul_nonneg (Nat.cast_nonneg _) hv) (by positivity))
    _ = _ := by ring

end YM.Integration.WilsonCurvatureRankRate
end
