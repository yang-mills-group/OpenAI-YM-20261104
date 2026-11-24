import YM.Integration.SignedGraphSoftWindow

namespace YM.Integration.FineBoundaryTransfer
open Filter IterationFour.Currency RegulatorWindowRemainder SignedGraphSoftWindow RG

variable {G : Gauge} {C : Family G}

/-- Affine growth on the native Wilson clock gives a uniform tangent bound
for the logarithm, even when the upper cutoff is arbitrarily far away. -/
theorem log_drift (C : Family G) (i top : ℕ) :
    Real.log (B C.path.levels top) - Real.log (B C.path.levels i) ≤
      G.slopeConstant * (C.S.scale top - C.S.scale i) / B C.path.levels i := by
  have hb := WardBin.hot C.path.levels i
  have hc := WardBin.hot C.path.levels top
  have hdiff : B C.path.levels top - B C.path.levels i =
      G.slopeConstant * (C.S.scale top - C.S.scale i) := by
    change (_ + _ * C.S.scale top) - (_ + _ * C.S.scale i) = _
    ring
  rw [← Real.log_div hc.ne' hb.ne', ← hdiff]
  refine (Real.log_le_sub_one_of_pos (div_pos hc hb)).trans_eq ?_
  field_simp

/-- A polynomial price in the actual fine-end coupling is paid across a
window of true logarithmic mesh age. All the regulator couplings keep their
original common cutoff and period. -/
theorem boundary_transfer (hC : C.Makes) {s t γ : ℝ} (ht : 0 ≤ t)
    {N period i top : ℕ} (hit : i ≤ top) (htN : top ≤ N)
    (hdrift : t * G.slopeConstant ≤ γ * B C.path.levels i)
    (hage : (s + t) * Real.log (B C.path.levels i) ≤ γ * (C.S.scale top - C.S.scale i)) :
    transfer C γ i top * g C N period top ^ (-t) ≤
      (4 : ℝ) ^ (t / 2) * weight C.path.levels s i := by
  have hb := WardBin.hot C.path.levels i
  have hc := WardBin.hot C.path.levels top
  have hscale : Monotone C.S.scale := monotone_nat_of_le_succ fun j => by
    rw [C.S.scale_succ]
    exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (C.S.block j).pos))
  have ha : 0 ≤ C.S.scale top - C.S.scale i := sub_nonneg.mpr (hscale hit)
  have hlog : t * (Real.log (B C.path.levels top) - Real.log (B C.path.levels i)) ≤
      γ * (C.S.scale top - C.S.scale i) := by
    calc
      _ ≤ t * (G.slopeConstant * (C.S.scale top - C.S.scale i) / B C.path.levels i) :=
        mul_le_mul_of_nonneg_left (log_drift C i top) ht
      _ = t * G.slopeConstant / B C.path.levels i * (C.S.scale top - C.S.scale i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hb).mpr hdrift) ha
  have hw : transfer C γ i top * B C.path.levels top ^ (t / 2) ≤
      weight C.path.levels s i := by
    rw [transfer_eq_age C γ hit, Real.rpow_def_of_pos hc, ← Real.exp_add]
    change _ ≤ gain (B C.path.levels i) ^ s
    rw [rpGain _ hb, Real.rpow_def_of_pos hb]
    exact Real.exp_le_exp.mpr (by linarith only [hlog, hage])
  have hband := actual_band hC N period top htN
  have hbound : g C N period top ^ (-t) ≤
      (4 : ℝ) ^ (t / 2) * B C.path.levels top ^ (t / 2) := by
    change gain (C.path.β N period top) ^ (-t) ≤ _
    rw [rpGain _ (stripe_pos hc hband), neg_neg, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hc.le]
    exact Real.rpow_le_rpow (stripe_pos hc hband).le hband.2 (by positivity)
  have htr : 0 ≤ transfer C γ i top := by
    rw [transfer_eq_age C γ hit]
    positivity
  calc
    _ ≤ transfer C γ i top * ((4 : ℝ) ^ (t / 2) * B C.path.levels top ^ (t / 2)) :=
      mul_le_mul_of_nonneg_left hbound htr
    _ = (4 : ℝ) ^ (t / 2) * (transfer C γ i top * B C.path.levels top ^ (t / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (Real.rpow_nonneg (by norm_num) _)

/-- Every sufficiently late stop and all sufficiently fine endpoints give
the same order-s bound from a polynomially expensive boundary at the actual
fine coupling and the native one-step signed forcing. -/
theorem uniform (hG : G.Simple) (hC : C.Makes) {s t γ A F : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hγ : 0 < γ) (hA : 0 ≤ A) (hF : 0 ≤ F) :
    ∃ K ≥ 0, ∀ᶠ i : ℕ in atTop, ∀ᶠ top : ℕ in atTop, ∀ N period : ℕ, top ≤ N →
      ∀ d : ℕ → ℝ, d top ≤ A * g C N period top ^ (-t) →
      (∀ j, i ≤ j → j < top →
        d j ≤ ((C.S.block j).val : ℝ) ^ (-γ) * d (j + 1) +
          F * g C N period (j + 1) ^ s) →
      d i ≤ K * g C N period i ^ s := by
  obtain ⟨k, hk, hforce⟩ := bounded_forcing hG hC hs hγ hF
  have h4 : 0 ≤ (4 : ℝ) ^ (t / 2) := Real.rpow_nonneg (by norm_num) _
  have h2 : 0 ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) _
  refine ⟨A * (4 : ℝ) ^ (t / 2) * (2 : ℝ) ^ s + k,
    add_nonneg (mul_nonneg (mul_nonneg hA h4) h2) hk, ?_⟩
  filter_upwards [(WardBin.bell C.path.levels hG).eventually_ge_atTop
    (t * G.slopeConstant / γ)] with i hi
  have hdrift : t * G.slopeConstant ≤ γ * B C.path.levels i := by
    simpa only [mul_comm] using (div_le_iff₀ hγ).mp hi
  filter_upwards [eventually_long C hγ i ((s + t) * Real.log (B C.path.levels i))]
    with top htop N period htN d hd hstep
  have htr : 0 ≤ transfer C γ i top := by
    rw [transfer_eq_age C γ htop.1]
    positivity
  have hpaid := boundary_transfer (N := N) (period := period) hC ht htop.1 htN hdrift htop.2
  have hb : transfer C γ i top * d top ≤
      A * (4 : ℝ) ^ (t / 2) * (2 : ℝ) ^ s * g C N period i ^ s := by
    calc
      _ ≤ transfer C γ i top * (A * g C N period top ^ (-t)) :=
        mul_le_mul_of_nonneg_left hd htr
      _ = A * (transfer C γ i top * g C N period top ^ (-t)) := by ring
      _ ≤ A * ((4 : ℝ) ^ (t / 2) * weight C.path.levels s i) :=
        mul_le_mul_of_nonneg_left hpaid hA
      _ ≤ A * ((4 : ℝ) ^ (t / 2) * ((2 : ℝ) ^ s * g C N period i ^ s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (g_weight hC (htop.1.trans htN) s hs).1 h4) hA
      _ = _ := by ring
  calc
    d i ≤ _ := hforce N period i top htop.1 htN d hstep
    _ ≤ A * (4 : ℝ) ^ (t / 2) * (2 : ℝ) ^ s * g C N period i ^ s +
          k * g C N period i ^ s := add_le_add hb le_rfl
    _ = _ := (add_mul _ _ _).symm

/-- The signed local bound, with any positive order reserve, suppresses every
fixed inverse power of the actual fine boundary coupling. -/
theorem eventual_small (hG : G.Simple) (hC : C.Makes) {p s t γ A F ε : ℝ}
    (hp : 0 ≤ p) (hps : p < s) (ht : 0 ≤ t) (hγ : 0 < γ)
    (hA : 0 ≤ A) (hF : 0 ≤ F) (hε : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ᶠ top : ℕ in atTop, ∀ N period : ℕ, top ≤ N →
      ∀ d : ℕ → ℝ, d top ≤ A * g C N period top ^ (-t) →
      (∀ j, i ≤ j → j < top →
        d j ≤ ((C.S.block j).val : ℝ) ^ (-γ) * d (j + 1) +
          F * g C N period (j + 1) ^ s) →
      d i ≤ ε * g C N period i ^ p := by
  have hs := hp.trans hps.le
  obtain ⟨K, hK, h⟩ := uniform hG hC hs ht hγ hA hF
  have h2 : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  filter_upwards [h, buy C.path.levels hG (K * (2 : ℝ) ^ s) (div_pos hε h2) hps]
    with i hi hbuy
  filter_upwards [hi, eventually_ge_atTop i] with top htop hit N period htN d hd hstep
  calc
    d i ≤ K * g C N period i ^ s := htop N period htN d hd hstep
    _ ≤ K * ((2 : ℝ) ^ s * weight C.path.levels s i) :=
      mul_le_mul_of_nonneg_left (g_weight hC (hit.trans htN) s hs).2 hK
    _ ≤ (ε / (2 : ℝ) ^ p) * weight C.path.levels p i := by rwa [← mul_assoc]
    _ ≤ (ε / (2 : ℝ) ^ p) * ((2 : ℝ) ^ p * g C N period i ^ p) :=
      mul_le_mul_of_nonneg_left (g_weight hC (hit.trans htN) p hp).1 (div_nonneg hε.le h2.le)
    _ = ε * g C N period i ^ p := by rw [← mul_assoc, div_mul_cancel₀ _ h2.ne']

end YM.Integration.FineBoundaryTransfer
