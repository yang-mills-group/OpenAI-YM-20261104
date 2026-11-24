import YM.Integration.FVA1Physical.Sources.StencilCosts

/-! A volume-independent polynomial bound for the physical stencil envelope
at a fixed field horizon and marker load. -/

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open Lattice RG Wilson Source Extra.Histories Extra.Multi Next.Foundations
open LocalLTE.Sail
open scoped BigOperators

noncomputable def horizonPrice (G : Gauge) (D : ℕ) : ℝ :=
  1 + ∑ d ∈ Finset.range (D + 1), BasisCost.price (localSection G d)

noncomputable def horizonDegree (G : Gauge) (D : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (D + 1), BasisCost.slots ((Labels.frames G).level d)

noncomputable def horizonPrefactor (G : Gauge) (D K : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (K + 1), ‖((k.factorial : ℂ)⁻¹)‖) *
    ((1 + (K : ℝ)) * horizonPrice G D) ^ K

theorem stencilCost_horizon {G : Gauge} (H : History G) (N d D : ℕ) (hd : d ≤ D)
    (v : ((Labels.frames G).level d).Coeff) (hv : ((Labels.frames G).level d).coeffSize v ≤ 1) :
    stencilCost H N d v ≤ horizonPrice G D * H.levels.clock.hatBeta N ^ horizonDegree G D := by
  let T := H.levels.clock
  let a := T.hatBeta N
  let F := (Labels.frames G).level d
  have ha : 1 ≤ a := (H.levels.fits.delayed N).le
  have hpos : 0 < T.hatCoupling N := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le ha))
  have hthreshold : T.hatCoupling N ≤ T.threshold N :=
    le_mul_of_one_le_right hpos.le (Real.one_le_exp (sq_nonneg _))
  have hsqrt : 1 ≤ Real.sqrt a := Real.one_le_sqrt.mpr ha
  have hta : (T.threshold N)⁻¹ ≤ a := calc
    _ ≤ (T.hatCoupling N)⁻¹ := inv_anti₀ hpos hthreshold
    _ = Real.sqrt a := inv_inv _
    _ ≤ a := by nlinarith only [Real.sq_sqrt (zero_le_one.trans ha),
      mul_nonneg (sub_nonneg.mpr hsqrt) (Real.sqrt_nonneg a)]
  have hd' : d ∈ Finset.range (D + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hdegree (j : F.Index) : (F.grades j).2 ≤ horizonDegree G D :=
    (Finset.le_sup (f := fun j : F.Index => (F.grades j).2) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun z _ => Nat.zero_le (BasisCost.slots ((Labels.frames G).level z))) hd')
  have hp : BasisCost.price (localSection G d) ≤ horizonPrice G D :=
    (Finset.single_le_sum (fun z _ => zero_le_one.trans (BasisCost.price_pos (localSection G z))) hd').trans
      (le_add_of_nonneg_left zero_le_one)
  have hc : F.coeffSize (F.scaled (T.threshold N)⁻¹ v) ≤ a ^ horizonDegree G D * F.coeffSize v := by
    unfold Labels.Frame.coeffSize
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Labels.Frame.scaled_apply, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr (hpos.le.trans hthreshold)) _)]
    exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (inv_nonneg.mpr (hpos.le.trans hthreshold)) hta
      _).trans (pow_le_pow_right₀ ha (hdegree j))) (norm_nonneg _)
  exact mul_le_mul hp (hc.trans (mul_le_of_le_one_right (pow_nonneg (zero_le_one.trans ha) _) hv))
    (BasisCost.coeff_nonneg _) ((zero_le_one.trans (BasisCost.price_pos _)).trans hp)

theorem stencilInsertion_horizon {G : Gauge} {H : History G} {N n : ℕ} {I : Type} [Fintype I]
    (Y : Batch H N n I) (D K : ℕ) (hd : ∀ j, Y.demand j ≤ D) (hK : Fintype.card I ≤ K)
    (hv : ∀ j, ((Labels.frames G).level (Y.demand j)).coeffSize (Y.voice j) ≤ 1) :
    stencilInsertionBound H N Y.demand Y.voice ≤
      horizonPrefactor G D K * H.levels.clock.hatBeta N ^ (horizonDegree G D * K) := by
  let a := H.levels.clock.hatBeta N
  let d := horizonDegree G D
  let b := (1 + (K : ℝ)) * horizonPrice G D
  have ha : 1 ≤ a := (H.levels.fits.delayed N).le
  have hp : 1 ≤ horizonPrice G D := le_add_of_nonneg_right (Finset.sum_nonneg
    fun j _ => zero_le_one.trans (BasisCost.price_pos (localSection G j)))
  have hb : 1 ≤ b := one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (Nat.cast_nonneg K)) hp
  have hs : ∑ j, stencilCost H N (Y.demand j) (Y.voice j) ≤ b * a ^ d := calc
    _ ≤ ∑ _ : I, horizonPrice G D * a ^ d :=
      Finset.sum_le_sum fun j _ => stencilCost_horizon H N (Y.demand j) D (hd j) (Y.voice j) (hv j)
    _ = (Fintype.card I : ℝ) * (horizonPrice G D * a ^ d) := by rw [Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    _ ≤ (1 + (K : ℝ)) * (horizonPrice G D * a ^ d) := mul_le_mul_of_nonneg_right
      ((Nat.cast_le.mpr hK).trans (le_add_of_nonneg_left zero_le_one))
      (mul_nonneg (zero_le_one.trans hp) (pow_nonneg (zero_le_one.trans ha) _))
    _ = _ := (mul_assoc ..).symm
  have ht : 0 ≤ ∑ j, stencilCost H N (Y.demand j) (Y.voice j) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (zero_le_one.trans (BasisCost.price_pos _)) (BasisCost.coeff_nonneg _)
  have hm : ∑ k ∈ Finset.range (Fintype.card I + 1), ‖((k.factorial : ℂ)⁻¹)‖ ≤
      ∑ k ∈ Finset.range (K + 1), ‖((k.factorial : ℂ)⁻¹)‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hK)) (fun _ _ _ => norm_nonneg _)
  have hb' : 1 ≤ b * a ^ d := one_le_mul_of_one_le_of_one_le hb (one_le_pow₀ ha)
  calc
    _ ≤ ∑ k ∈ Finset.range (Fintype.card I + 1), ‖((k.factorial : ℂ)⁻¹)‖ * (b * a ^ d) ^ K := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (pow_le_pow_left₀ ht hs k).trans (pow_le_pow_right₀ hb' ((Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk)).trans hK))
    _ ≤ (∑ k ∈ Finset.range (K + 1), ‖((k.factorial : ℂ)⁻¹)‖) * (b * a ^ d) ^ K := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hm (pow_nonneg (zero_le_one.trans hb') _)
    _ = _ := by rw [mul_pow, ← pow_mul, ← mul_assoc]; rfl

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
