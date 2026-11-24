import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic
/-!
# Power expenditures along receding detector geometries

Results here are analysis only. Ultimately put `T asymp g^(-B)` in every estimate;
covers e.g. exact `T=g^(-B)` or using the calibrated scale if ratio t/g→1.
Buy **B** after horizon & required final P; buy precision p after B. No large p
independent of B spent through estimating all higher-order terms. See application for the
relation of r and g; here r-cost abstract, use assumption r smaller than every power of g.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
namespace Budget
open Function Filter Real Set
open scoped Topology NNReal BigOperators
variable {B ε : ℝ} (hB : 0 < B) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
local notation "ℓ" => (𝓝[>] (0:ℝ))

-- standing for T in a fixed multiplicative comparability region
abbrev receding (g B a b T : ℝ) := a*g^(-B) ≤ T ∧ T ≤ b*g^(-B)
include hB ha
lemma upwards (T₀ : ℝ) : ∀ᶠ g in ℓ, ∀ T, a*g^(-B) ≤ T → T₀ ≤ T :=
    (( (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hB)).const_mul_atTop ha).eventually_ge_atTop T₀).mono
      fun _ hi _ ht => hi.trans ht

omit hB ha in
private lemma log_budget {α : ℝ} (n : ℕ) (hp : 0 < α) :
    ∀ᶠ T in atTop, (1+log T)^n ≤ 2^n*T^α := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop (n:ℝ) hp).bound (show (0:ℝ)<1 from zero_lt_one),
    eventually_gt_atTop (0:ℝ), tendsto_log_atTop.eventually_ge_atTop 1]
    with T ht hT hx
  rw [Real.rpow_natCast, one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at ht
  calc
    _ ≤ (2*log T)^n := by gcongr; linarith
    _ ≤ _ := by rw [mul_pow]; gcongr

include hb
lemma trade_less (he : 0 < ε) (C : ℝ) (hC : 0 ≤ C) (n : ℕ) {α q : ℝ} (h : B*q < α) :
    ∀ᶠ g in ℓ, ∀ T : ℝ, receding g B a b T → C*g^α*T^q*(1+log T)^n ≤ ε := by
  let t := (α-B*q)/(2*B)
  have ht : 0 < t := div_pos (sub_pos.mpr h) (by positivity)
  let d := α + (-B)*(q+t)
  have hp : 0 < d := by
    have hh : d=(α-B*q)/2 := by unfold d t; field_simp; ring
    rw [hh]; linarith
  let D := max (a^(q+t)) (b^(q+t))
  have hw : Tendsto (fun g:ℝ => C*2^n*D*g^d) ℓ (𝓝 0) := by
    have hZ : Tendsto (fun g:ℝ => g^d) ℓ (𝓝 0) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      simpa only [Real.zero_rpow hp.ne'] using ((Real.continuousAt_rpow_const 0 d (Or.inr hp.le)).tendsto)
    simpa only [mul_zero] using hZ.const_mul (C*2^n*D)
  have hc : ∀ᶠ g in ℓ, ∀ T : ℝ, a*g^(-B) ≤ T → (1+log T)^n ≤ 2^n*T^t := by
    obtain ⟨T₀,h₀⟩ := eventually_atTop.mp (log_budget n ht)
    exact (upwards hB ha T₀).mono fun i hi T he => h₀ T (hi T he)
  filter_upwards [hc, hw.eventually_lt_const he, self_mem_nhdsWithin] with g hc hx hg T hT
  have hz : 0 < g := hg
  have hs : 0 < T := lt_of_lt_of_le (by positivity : 0 < a*g^(-B)) hT.1
  have hs' : T^(q+t) ≤ D*g^((-B)*(q+t)) := by
    rw [Real.rpow_mul hz.le]
    by_cases h : 0 ≤ q+t
    · calc
        _ ≤ (b*g^(-B))^(q+t) := Real.rpow_le_rpow hs.le hT.2 h
        _ = _ := mul_rpow (le_of_lt hb) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
    · calc
        _ ≤ (a*g^(-B))^(q+t) := Real.rpow_le_rpow_of_nonpos (by positivity) hT.1 (le_of_not_ge h)
        _ = _ := mul_rpow (le_of_lt ha) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)
  calc
    _ ≤ C*g^α*T^q*(2^n*T^t) := by gcongr; exact hc T hT.1
    _ = C*2^n*g^α*T^(q+t) := by rw [Real.rpow_add hs]; ring
    _ ≤ C*2^n*g^α*(D*g^((-B)*(q+t))) := by gcongr
    _ = C*2^n*D*g^d := by unfold d; rw [Real.rpow_add hz]; ring -- annotate coefficient
    _ ≤ ε := hx.le

lemma trade (C : ℝ) (hC : 0 ≤ C) (n : ℕ) {α q γ m : ℝ}
    (h : B*(q-m) < α-γ) :
    ∀ᶠ g in ℓ, ∀ T : ℝ, receding g B a b T → C*g^α*T^q*(1+log T)^n ≤ g^γ*T^m := by
  filter_upwards [trade_less hB ha hb zero_lt_one C hC n h, self_mem_nhdsWithin] with g hc hg T hT
  have hz : 0 < g := hg
  have hs : 0 < T := lt_of_lt_of_le (by positivity : 0 < a*g^(-B)) hT.1
  calc
    _ = g^γ*T^m*(C*g^(α-γ)*T^(q-m)*(1+log T)^n) := by
      rw [Real.rpow_sub hz, Real.rpow_sub hs]; field_simp
    _ ≤ g^γ*T^m*1 := by gcongr; exact hc T hT
    _ = _ := mul_one _

end Budget
end YM.FVA2.GradedFar
