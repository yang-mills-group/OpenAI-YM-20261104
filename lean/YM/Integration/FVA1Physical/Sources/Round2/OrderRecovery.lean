import YM.Integration.FVA1Physical.Sources.Round2.ClockOrder
import YM.Integration.FVA1Physical.Sources.Round2.AllFlagStage

/-! Recover a prescribed physical power uniformly in the initial cutoff and
period on a bounded window by choosing the underlying C18 order in advance. -/

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open Lattice RG Wilson RG.Supply Input Org Source Extra.Histories LocalLTE.Sail ConnectedActivityE6
open OPE.Therm YM.Integration.FVA1Physical.Round2
open scoped BigOperators

noncomputable def upgradedOrder (G : Gauge) (D K p : ℕ) : ℕ :=
  p + 2 * (horizonDegree G D * K)

noncomputable def slopeCap (K : ℕ) (T : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (K + 1), ‖((k.factorial : ℂ)⁻¹)‖) * (1 + T) ^ K

private theorem markerSlope_le {k K : ℕ} (hk : k ≤ K) {t T : ℝ} (ht : 0 ≤ t) (hT : t ≤ T) :
    markerSlope k t ≤ slopeCap K T := by
  have h1 : 1 ≤ 1 + T := le_add_of_nonneg_right (ht.trans hT)
  have hs : (Finset.range (k + 1)).erase 0 ⊆ Finset.range (K + 1) :=
    (Finset.erase_subset ..).trans (Finset.range_mono (Nat.succ_le_succ hk))
  unfold markerSlope slopeCap
  rw [Finset.sum_mul]
  apply (Finset.sum_le_sum (g := fun j => ‖((j.factorial : ℂ)⁻¹)‖ * (1 + T) ^ K) ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hs fun j _ _ => mul_nonneg (norm_nonneg _)
      (pow_nonneg (zero_le_one.trans h1) _))
  intro j hj
  have hj' := Finset.mem_range.mp (hs hj)
  exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ ht (hT.trans (le_add_of_nonneg_left zero_le_one))
    _).trans (pow_le_pow_right₀ h1 (show j - 1 ≤ K by omega))) (norm_nonneg _)

noncomputable def uniformGasCost (G : Gauge) (D K W p : ℕ) : ℝ :=
  horizonPrefactor G D K * ((1 + G.slopeConstant) ^ W * 2) ^ (horizonDegree G D * K) *
    slopeCap K (2 * (K : ℝ) * 2 ^ (upgradedOrder G D K p + 1)) * (2 * K)

theorem recoverPhysicalOrder {G : Gauge} {X : Metals G} {D' : Rolls X.p} {A : Alloy X D'} {P : Bolt A}
    (hG : G.Simple) (hp : Poetry (Issue.trail P).levels) {i N n : ℕ} (hi : i < N)
    (W D K p : ℕ) (hw : N - (i + 1) ≤ W) {I : Type} [Fintype I]
    (Y : Batch (Issue.trail P) N n I) (hd : ∀ j, Y.demand j ≤ D) (hk : Fintype.card I ≤ K)
    (hv : ∀ j, ((Labels.frames G).level (Y.demand j)).coeffSize (Y.voice j) ≤ 1) :
    gasReadoutCost (i := i) Y (upgradedOrder G D K p) K ≤
      uniformGasCost G D K W p * Coat.gStep ((Issue.trail P).rep N n (i + 1)).beta ^ (p + 1) := by
  let H := Issue.trail P
  let β := (H.rep N n (i + 1)).beta
  let g := Coat.gStep β
  let J := horizonDegree G D * K
  let r := upgradedOrder G D K p
  let c := (1 + G.slopeConstant) ^ W * 2
  let T := 2 * (K : ℝ) * (2 : ℝ) ^ (r + 1)
  let t := 2 * (K : ℝ) * g ^ (r + 1)
  have hh := (P.choice.represents N n (i + 1) hi).band.1
  have hβlo : (1 / 2 : ℝ) ≤ β := by
    change H.levels.clock.hatBeta (i + 1) / 2 ≤ β at hh
    linarith only [hh, H.levels.fits.delayed (i + 1)]
  have hβ : 0 < β := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hβlo
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have hroot := Real.sqrt_le_sqrt (show (1 / 2 : ℝ)^2 ≤ β by linarith only [hβlo])
  rw [Real.sqrt_sq (by norm_num)] at hroot
  have hg2 : g ≤ 2 := (inv_anti₀ (by norm_num : (0 : ℝ) < 1/2) hroot).trans_eq (by norm_num)
  have ht : 0 ≤ t := mul_nonneg (by positivity) (pow_nonneg hg.le _)
  have hT : t ≤ T := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.le hg2 _) (by positivity)
  have hcost := stencilInsertion_horizon Y D K hd hk hv
  have hbar := windowBeta_actual P.choice hp hG (n := n) (Nat.succ_le_of_lt hi) hw
  have hfee : 0 ≤ horizonPrefactor G D K := by
    have hprice : 1 ≤ horizonPrice G D := le_add_of_nonneg_right (Finset.sum_nonneg
      fun d _ => zero_le_one.trans (Extra.Multi.BasisCost.price_pos (Next.Foundations.localSection G d)))
    unfold horizonPrefactor
    positivity
  have hc : 0 ≤ c := mul_nonneg (pow_nonneg (add_nonneg zero_le_one (Gauge.slopeConstant_pos hG).le) _) zero_le_two
  have hseed : stencilInsertionBound H N Y.demand Y.voice ≤ (horizonPrefactor G D K * c^J) * β^J := by
    rw [mul_assoc, ← mul_pow]
    exact hcost.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (zero_le_one.trans (H.levels.fits.delayed N).le) hbar J) hfee)
  have hsl := markerSlope_le hk ht hT
  have hsl0 : 0 ≤ markerSlope (Fintype.card I) t :=
    Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (pow_nonneg ht _)
  have hturn : β * g ^ 2 = 1 := by
    change β * (Real.sqrt β)⁻¹ ^ 2 = 1
    rw [inv_pow, Real.sq_sqrt hβ.le, mul_inv_cancel₀ hβ.ne']
  have hcancel : β ^ J * g ^ (r + 1) = g ^ (p + 1) := by
    have hr : r + 1 = 2 * J + (p + 1) := by dsimp [r, J, upgradedOrder]; omega
    rw [hr, pow_add, pow_mul g 2 J, ← mul_assoc, ← mul_pow, hturn, one_pow, one_mul]
  have hcast : (g ^ ((r : ℝ) + 1) : ℝ) = g ^ (r + 1) := by
    rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add, Real.rpow_natCast]
  change stencilInsertionBound H N Y.demand Y.voice *
    (markerSlope (Fintype.card I) (2 * K * g ^ ((r : ℝ) + 1)) *
      (2 * K * g ^ ((r : ℝ) + 1))) ≤ _
  rw [hcast]
  apply (mul_le_mul hseed (mul_le_mul_of_nonneg_right hsl ht) (mul_nonneg hsl0 ht)
    (mul_nonneg (mul_nonneg hfee (pow_nonneg hc J)) (pow_nonneg hβ.le J))).trans_eq
  change (horizonPrefactor G D K * c^J * β^J) * (slopeCap K T * (2 * K * g^(r+1))) =
    (horizonPrefactor G D K * c^J * slopeCap K T * (2 * K)) * g^(p+1)
  rw [← hcancel]
  ring

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
