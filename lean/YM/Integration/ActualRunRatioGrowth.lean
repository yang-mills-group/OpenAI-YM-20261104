import YM.Integration.ActualRunStationaryQuotePrices

/-! Polynomial costs of the actual block ratio are paid by the original
Run's retained dusk receipt. No new schedule, Prepaid witness, or late-event
hypothesis is introduced. This does not price an arbitrary post-L tariff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunRatioGrowth
open Filter RG PhysicalNext.Repeat.Legato
open scoped Topology

private lemma power_of_weight {x y L : ℝ} {n q : ℕ}
    (hx : 0 < x) (hxy : x ≤ y) (hL : 0 ≤ L)
    (h : y⁻¹ * L^n * (x^q)⁻¹ ≤ (y^q)⁻¹) : L^n ≤ y := by
  have hy : 0 < y := hx.trans_le hxy
  have hw : (y^q)⁻¹ ≤ (x^q)⁻¹ :=
    inv_anti₀ (pow_pos hx _) (pow_le_pow_left₀ hx.le hxy _)
  have hh : y⁻¹ * L^n * (y^q)⁻¹ ≤ (y^q)⁻¹ :=
    (mul_le_mul_of_nonneg_left hw
      (mul_nonneg (inv_nonneg.mpr hy.le) (pow_nonneg hL _))).trans h
  have hp : y⁻¹ * L^n ≤ 1 :=
    (mul_le_mul_iff_left₀ (inv_pos.mpr (pow_pos hy _))).mp (by simpa only [one_mul] using hh)
  simpa only [mul_one] using (inv_mul_le_iff₀ hy).mp hp

/-- The original purchase controls powers up to the current lower stage.
The upper temperature and block ratio are those of the same step. -/
theorem ratio_power_le {G : Gauge} (R : Run G) (hG : G.Simple)
    (m d : ℕ) (hd : d ≤ R.alloy.B.a.clock.J m) :
    ((R.alloy.B.a.S.block m).val : ℝ)^(d+1) ≤
      R.alloy.B.a.clock.hatBeta (m+1) := by
  have h := R.bought R.T R.tuning.receipts R.t R.accepts R.stories
    R.doors R.makes R.carries R.books
  obtain ⟨Kc,L,V,W,hD,hV,hP,hL⟩ := h.2.2.2.2.2.2.1
  have hw := ((hD (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m)
    (Push.PriceCompiler.step_paid R.alloy.B.a m)
    (R.alloy.B.a.clock.hatBeta m) (R.alloy.B.valid.pays m)).2 d hd).2
  change (Pressure.betaF G (R.alloy.B.a.clock.hatBeta m)
      (R.rolls.L (R.alloy.B.a.clock.J (m+1))))⁻¹ *
    ((R.rolls.L (R.alloy.B.a.clock.J (m+1))).val : ℝ)^(d+1) *
    ((R.alloy.B.a.clock.hatBeta m)^MergeProof.winter G d)⁻¹ ≤
    ((Pressure.betaF G (R.alloy.B.a.clock.hatBeta m)
      (R.rolls.L (R.alloy.B.a.clock.J (m+1))))^MergeProof.winter G d)⁻¹ at hw
  rw [← Push.PriceCompiler.beta_eq R.alloy.B.valid m,
    ← Push.PriceCompiler.block_eq R.alloy.B.valid m] at hw
  exact power_of_weight (WardBin.hot R.alloy.B.a m)
    (Push.Corrected.Last.band_le R.alloy.B.a hG (Nat.le_succ m))
    (Nat.cast_nonneg _) hw

/-- Every fixed polynomial in the original ratio is negligible against a
positive power of the hatted fine coupling. -/
theorem ratio_hat_tendsto {G : Gauge} (R : Run G) (hG : G.Simple)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m : ℕ => ((R.alloy.B.a.S.block m).val : ℝ)^k *
      R.alloy.B.a.clock.hatCoupling (m+1)^ε) atTop (𝓝 0) := by
  let A := R.alloy.B.a
  obtain ⟨K,hK⟩ := exists_nat_gt ((4*(k:ℝ))/ε)
  have ht := (tendsto_rpow_neg_atTop (show 0 < ε/4 by positivity)).comp
    ((WardBin.bell A hG).comp (tendsto_add_atTop_nat 1))
  apply squeeze_zero' (Eventually.of_forall fun m =>
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) k)
      (Real.rpow_nonneg (WardBin.stepG A (m+1)).le ε)) ?_ ht
  filter_upwards [A.fits.deep.eventually_ge_atTop K] with m hm
  have hp := WardBin.hot A (m+1)
  have hβ : 1 ≤ A.clock.hatBeta (m+1) := (A.fits.delayed _).le
  have hJ : (K:ℝ) ≤ A.clock.J m := by exact_mod_cast hm
  have hk : 4*(k:ℝ) < ε*K := by
    simpa only [mul_comm ε] using (div_lt_iff₀ hε).mp hK
  have he : (k:ℝ)/((A.clock.J m:ℝ)+1) ≤ ε/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hJ hε.le]
  have hpow := ratio_power_le R hG m (A.clock.J m) le_rfl
  have hroot : ((A.S.block m).val:ℝ) ≤
      A.clock.hatBeta (m+1)^((1:ℝ)/((A.clock.J m:ℝ)+1)) := by
    have hh := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) _)
      hpow (show 0 ≤ (1:ℝ)/((A.clock.J m:ℝ)+1) by positivity)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)] at hh
    have hz : ((A.clock.J m+1:ℕ):ℝ)*((1:ℝ)/((A.clock.J m:ℝ)+1))=1 := by
      push_cast
      field_simp
    rw [hz,Real.rpow_one] at hh
    exact hh
  have hupper := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hroot k)
    (Real.rpow_nonneg (WardBin.stepG A (m+1)).le ε)
  have hid : (A.clock.hatBeta (m+1)^((1:ℝ)/((A.clock.J m:ℝ)+1)))^k *
      A.clock.hatCoupling (m+1)^ε =
      A.clock.hatBeta (m+1)^((k:ℝ)/((A.clock.J m:ℝ)+1)-ε/2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    unfold Calendar.hatCoupling
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hp.le, ← Real.rpow_mul hp.le,
      ← Real.rpow_add hp]
    congr 1
    ring
  exact hupper.trans (hid.trans_le
    (Real.rpow_le_rpow_of_exponent_le hβ (by linarith)))

/-- Actual fine-Rep payment, uniform over the cutoff and period, with the
original Run and ratio. Only a fixed polynomial ratio cost is claimed. -/
theorem actual_payment {G : Gauge} (R : Run G) (hG : G.Simple)
    (k : ℕ) (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      c*((R.alloy.B.a.S.block m).val:ℝ)^k ≤
        (Next.SectorChange.coupling ((R.family.path.rep N period (m+1)).beta))^(-ε) := by
  have ht := (ratio_hat_tendsto R hG k ε hε).const_mul (c*(2:ℝ)^ε)
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const zero_lt_one] with m hm N period hN
  let g := Pert.Asymptotics.regulatorRun R.family N period (m+1)
  have hg : 0 < g := IterationFour.Currency.g_pos R.makes N period (m+1) (by omega)
  have hgain := (IterationFour.Currency.hat_g R.makes N period (m+1) (by omega)).2
  have hgp : g^ε ≤ (2:ℝ)^ε * R.alloy.B.a.clock.hatCoupling (m+1)^ε := by
    calc
      _ ≤ (2*R.alloy.B.a.clock.hatCoupling (m+1))^ε :=
        Real.rpow_le_rpow hg.le hgain hε.le
      _ = _ := Real.mul_rpow (by norm_num) (WardBin.stepG R.alloy.B.a (m+1)).le
  have hpaid : (c*((R.alloy.B.a.S.block m).val:ℝ)^k)*g^ε ≤ 1 := by
    calc
      _ ≤ (c*((R.alloy.B.a.S.block m).val:ℝ)^k)*
          ((2:ℝ)^ε*R.alloy.B.a.clock.hatCoupling (m+1)^ε) :=
        mul_le_mul_of_nonneg_left hgp (mul_nonneg hc (pow_nonneg (Nat.cast_nonneg _) _))
      _ = (c*(2:ℝ)^ε)*(((R.alloy.B.a.S.block m).val:ℝ)^k*
          R.alloy.B.a.clock.hatCoupling (m+1)^ε) := by ring
      _ ≤ 1 := hm
  change c*((R.alloy.B.a.S.block m).val:ℝ)^k ≤ g^(-ε)
  rw [Real.rpow_neg hg.le, ← one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hg ε)).mpr hpaid

end YM.Integration.ActualRunRatioGrowth
end
