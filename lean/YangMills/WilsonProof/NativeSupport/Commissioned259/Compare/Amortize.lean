import YangMills.WilsonProof.NativeSupport.Commissioned259.Matched
import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Overtime

/-! # Expend T/log-T and g prices, preserving a fixed T reserve before inversion -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Comparing
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {I : Type*} {X : Filter I}

lemma pace (h : G.Simple) : Tendsto (g0 G) (𝓝[>] (0:ℝ)) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]; exact ⟨g0_zero h,g0_pos h⟩

/-- `r` itself smaller than any power paid in these estimates. -/
lemma length (h : G.Simple) (d : ℝ) : (fun r:ℝ=>r) =O[𝓝[>] 0] (fun r=>g0 G r ^ d) := by
  let Z (x:ℝ) := G.slopeConstant*Real.log x⁻¹
  have h0 := Gauge.slopeConstant_pos h
  have hi : Tendsto Z (𝓝[>] (0:ℝ)) atTop := (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).const_mul_atTop h0
  obtain ht := ((isLittleO_exp_neg_mul_rpow_atTop (inv_pos.mpr h0) (-(d/2))).comp_tendsto hi).isBigO
  refine ht.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with i hi
    change Real.exp ( - G.slopeConstant⁻¹ * Z i) = i; unfold Z; rw [ ← mul_assoc, neg_mul, inv_mul_cancel₀ h0.ne', neg_one_mul, Real.log_inv, neg_neg, Real.exp_log hi]
  filter_upwards [hi.eventually_gt_atTop 0] with i hi
  change Z i ^ (-(d / 2)) = (Real.sqrt (Z i))⁻¹ ^ d
  rw [← Real.rpow_neg_eq_inv_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hi.le]
  congr 1; ring

variable {g T : I → ℝ} (hg : Tendsto g X (𝓝[>] 0)) (ht : ∀ᶠ i in X, 1 ≤ T i)
    {B : ℝ} (hB : 0 < B) (Hs : T =Θ[X] fun i=>g i ^ (-B))

include hg
lemma now : ∀ᶠ i in X, 0 < g i := hg.eventually self_mem_nhdsWithin
lemma near : ∀ᶠ i in X, g i ≤ 1 := ((tendsto_nhdsWithin_iff.mp hg).1.eventually (ge_mem_nhds zero_lt_one))
lemma smaller {p q : ℝ} (hp : q≤p) : (fun i=>g i ^ p)=O[X] (fun i=>g i ^ q) := by
  refine IsBigO.of_bound' ?_; filter_upwards [now hg, near hg] with i h hg
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_exponent_ge h hg hp

include ht Hs
lemma clock_scale (p q : ℝ) : (fun i=> T i ^ p * g i ^ q) =Θ[X] (fun i=>g i ^ (q-B*p)) := by
  refine ((IsTheta.rpow (r:=p) ((show ∀ᶠ i in X,0≤T i from ht.mono fun i h=> zero_le_one.trans h))
    ((show ∀ᶠ i in X,0≤g i^(-B) from (now hg).mono fun i h=> by positivity)) Hs).mul
      (isTheta_refl (fun i=>g i ^ q) X)).trans_eventuallyEq ?_
  filter_upwards [now hg] with i hi; rw [ ← Real.rpow_mul hi.le, ← Real.rpow_add hi ]; congr 1; ring
include hB
lemma soaring : Tendsto T X atTop := by
  have h : Tendsto (fun i=>‖g i ^ (-B)‖) X atTop := ((tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hB)).comp hg).congr'
    ((now hg).mono fun i hi=> (Real.norm_of_nonneg (by positivity : 0 ≤ g i ^ (-B))).symm)
  exact (Hs.tendsto_norm_atTop_iff.mpr h).congr' (ht.mono fun i hi=>Real.norm_of_nonneg (zero_le_one.trans hi))
lemma log_allowance (a : ℕ) : (fun i=>logs T i ^ a)=O[X] fun i=> (g i) ^ (-(1:ℝ)) := by
  have hs := soaring hg ht hB Hs
  obtain hp : (fun i=> Real.log (T i) ^ a)=O[X] fun i=>T i ^ B⁻¹ := by
    have hp := isLittleO_log_rpow_rpow_atTop (a : ℝ) (inv_pos.mpr hB); simp_rw [Real.rpow_natCast] at hp; exact hp.isBigO.comp_tendsto hs
  have hu : logs T =O[X] fun i=>Real.log (T i) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [ (Real.tendsto_log_atTop.comp hs).eventually_ge_atTop 1 ] with i hi
    change 1 ≤ Real.log (T i) at hi
    unfold logs; rw [Real.norm_of_nonneg (by linarith),Real.norm_of_nonneg (by linarith)]; linarith
  apply (hu.pow a).trans (hp.trans ?_)
  simpa only [Real.rpow_zero, mul_one, zero_sub, mul_inv_cancel₀ hB.ne'] using (clock_scale hg ht Hs B⁻¹ 0).1

/-- target price: leave T^{-h-η} before inverse. -/
def margin (P : ℕ) (h : ℕ) (η : ℝ) (g T : I → ℝ) (i : I) := T i ^ (-((h:ℝ)+η)) * (g i)^P
omit hB in
lemma exchange (p h : ℕ) (η : ℝ) : margin p h η g T =Θ[X] fun i => g i ^ ((p:ℝ)+B*(h+η)) := by
  unfold margin; convert clock_scale hg ht Hs (-(h+η)) (p:ℝ) using 1 <;> ext i <;> simp <;> ring

/-- One convenient clock inequality. Consume the logarithmic powers with one g power. -/
lemma leverage (P h : ℕ) (η a b : ℝ) (hh : P+B*(h+η)+1 ≤ b-B*a) (z : ℕ) :
    (fun i=> (T i ^ a * g i ^ b) * logs T i ^ z) =O[X] margin P h η g T := by
  refine (((clock_scale hg ht Hs a b).1.mul (log_allowance hg ht hB Hs z)).trans ?_).trans (exchange hg ht Hs P h η).2
  refine (smaller hg (show (P:ℝ)+B*(h+η) ≤ b-B*a + -1 by linarith)).congr' ?_ (EventuallyEq.refl ..)
  exact (now hg).mono fun i h=> Real.rpow_add h _ _

/- Delta terms of the M3 estimate. -/
variable {E : Type*} [Norm E] {w : I→E} (P h D p : ℕ) {η : ℝ}
include P h D p η
lemma turns (hp : (P:ℝ)+B*((D:ℝ)+h+η)+1 ≤ p+1) (f : Fare T X (fun i=> T i ^ D * g i ^ (p+1)) w) : w =O[X] margin P h η g T := by
  obtain ⟨z,hz⟩ := f
  refine hz.trans ?_
  simpa only [Real.rpow_natCast] using (leverage hg ht hB Hs P h η D (p+1:ℕ) (by push_cast; linarith) z)

-- formal M2 residual price also has TWO separate rates
omit D
lemma recrop (hp : (P:ℝ)+B*((h:ℝ)+η)+1 ≤ p+1) (hb : P+1 ≤ B*(1-η))
    (H : Fare T X (fun i=> ((T i)⁻¹)^(h+1) + g i^(p+1)) w) : w =O[X] margin P h η g T := by
  obtain ⟨z,hz⟩ := H; simp_rw [add_mul] at hz; refine hz.trans (IsBigO.add ?_ ?_)
  · refine (leverage hg ht hB Hs P h η (-(↑(h+1:ℕ):ℝ)) 0 (by push_cast; linarith) z).congr' ?_ (EventuallyEq.refl ..)
    filter_upwards [ht] with i hi; rw [Real.rpow_neg (zero_le_one.trans hi), Real.rpow_zero,mul_one,Real.rpow_natCast,inv_pow]
  simpa only [Real.rpow_natCast,Real.rpow_zero,one_mul] using leverage hg ht hB Hs P h η 0 (p+1:ℕ) (by push_cast; linarith) z

include D
omit p
lemma spatial (hSt : (P:ℝ)+D+1 ≤ B*(1-η)) {r : I → ℝ} (hr : ∀ a:ℝ,r =O[X] fun i=> g i^a)
    (H : w =O[X] fun i=> ((g i)⁻¹)^D*( r i * T i + ((T i)⁻¹)^(h+1))) : w =O[X] margin P h η g T := by
  simp_rw [mul_add] at H; apply H.trans (IsBigO.add ?_ ?_)
  · let k:ℝ := P + D + B*(h+η+1) + 1
    refine ((isBigO_refl (fun i=> ((g i)⁻¹)^D) X).mul ((hr (k:ℝ)).mul (isBigO_refl T X))).trans ?_
    refine (leverage hg ht hB Hs P h η 1 (k-D) (by unfold k; linarith) 0).congr' ?_ (EventuallyEq.refl ..)
    filter_upwards [now hg] with i hi; rw [pow_zero,mul_one,Real.rpow_sub hi,Real.rpow_one,Real.rpow_natCast,inv_pow, div_eq_mul_inv]; ring
  refine (leverage hg ht hB Hs P h η (-(↑(h+1:ℕ):ℝ)) (-(D:ℝ)) (by push_cast; linarith) 0).congr' ?_ (EventuallyEq.refl ..)
  filter_upwards [ht,now hg] with i hi h; simp_rw [pow_zero,mul_one,Real.rpow_neg h.le,Real.rpow_neg (zero_le_one.trans hi),Real.rpow_natCast,inv_pow,mul_comm]
end YM.FVA2.GradedFar259.Comparing
