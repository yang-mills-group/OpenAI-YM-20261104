import YM.Integration.WilsonAdmissionHeight

/-! Fixed-power measured windows on the same schedule. K is fixed before
radius, tests, fields, cutoffs and replicas. This preserves the existing
fifth-power construction and does not identify its eighth-power room with
an enlarged room for arbitrary K. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonMeasuredWindow

open Filter Set OPE
open WilsonMeasuredAdmission (mast mast_pos mast_gt_one mast_monotone)
open scoped Topology

variable {G : Gauge} (A : RG.Levels G) (hG : G.Simple) (K : ℕ)
include hG

lemma weighted_log_tendsto :
    Tendsto (fun k => A.S.a k * WilsonAdmissionScale.logarithm A k ^ K)
      atTop (𝓝 0) := by
  have hlog := (Real.tendsto_log_atTop.comp
    (WilsonAdmissionScale.logarithm_tendsto A hG)).eventually_ge_atTop (K : ℝ)
  have hupper : ∀ᶠ k in atTop,
      A.S.a k * WilsonAdmissionScale.logarithm A k ^ K ≤ Next.Rank.Station.gap A 1 k := by
    filter_upwards [hlog] with k hk
    apply mul_le_mul_of_nonneg_left ?_ (A.S.a_pos k).le
    change WilsonAdmissionScale.logarithm A k ^ K ≤ A.clock.monitor k ^ (1 : ℝ)
    rw [Real.rpow_one]
    have he : WilsonAdmissionScale.logarithm A k ^ K =
        Real.exp ((K : ℝ) * Real.log (WilsonAdmissionScale.logarithm A k)) := by
      simpa only [Real.exp_log (WilsonAdmissionScale.logarithm_pos A k)] using
        (Real.exp_nat_mul (Real.log (WilsonAdmissionScale.logarithm A k)) K).symm
    rw [he]
    apply Real.exp_le_exp.mpr
    change (K : ℝ) * Real.log (WilsonAdmissionScale.logarithm A k) ≤
      Real.log (WilsonAdmissionScale.logarithm A k) ^ 2
    change (K : ℝ) ≤ Real.log (WilsonAdmissionScale.logarithm A k) at hk
    have hx := mul_le_mul_of_nonneg_right hk ((Nat.cast_nonneg K).trans hk)
    nlinarith
  exact squeeze_zero' (.of_forall fun k =>
    mul_nonneg (A.S.a_pos k).le (pow_nonneg (WilsonAdmissionScale.logarithm_pos A k).le _))
    hupper (Next.Rank.Station.gap_rate A hG 1)

lemma weighted_mast_tendsto :
    Tendsto (fun k => A.S.a k * mast A k ^ K) atTop (𝓝 0) := by
  have hlarge := (WilsonAdmissionScale.logarithm_tendsto A hG).eventually_ge_atTop 2
  have hzero := (weighted_log_tendsto A hG K).const_mul ((2 : ℝ) ^ K)
  rw [mul_zero] at hzero
  apply squeeze_zero' (.of_forall fun k =>
    mul_nonneg (A.S.a_pos k).le (pow_nonneg (mast_pos A k).le _)) ?_ hzero
  filter_upwards [hlarge] with k hk
  have hpow : mast A k ^ K ≤ (2 : ℝ) ^ K * WilsonAdmissionScale.logarithm A k ^ K := by
    calc
      mast A k ^ K ≤ (2 * WilsonAdmissionScale.logarithm A k) ^ K :=
        pow_le_pow_left₀ (mast_pos A k).le (by dsimp only [mast]; linarith) K
      _ = (2 : ℝ) ^ K * WilsonAdmissionScale.logarithm A k ^ K := mul_pow _ _ _
  exact (mul_le_mul_of_nonneg_left hpow (A.S.a_pos k).le).trans_eq (by ring)

private lemma exists_stop {r : ℝ} (hr : 0 < r) :
    ∃ k : ℕ, A.S.a k * mast A k ^ K ≤ r :=
  ((weighted_mast_tendsto A hG K).eventually (gt_mem_nhds hr)).exists.imp fun _ h => h.le

/-- Least stop meeting the native fixed K-power window. Zero outside the
positive length domain is only a total-function convention. -/
def stop (r : ℝ) : ℕ := if hr : 0 < r then Nat.find (exists_stop A hG K hr) else 0

lemma stop_spec {r : ℝ} (hr : 0 < r) :
    A.S.a (stop A hG K r) * mast A (stop A hG K r) ^ K ≤ r := by
  rw [stop, dif_pos hr]
  exact Nat.find_spec (exists_stop A hG K hr)

private lemma stop_min {r : ℝ} (hr : 0 < r) {k : ℕ} (hk : k < stop A hG K r) :
    r < A.S.a k * mast A k ^ K := by
  rw [stop, dif_pos hr] at hk
  exact lt_of_not_ge (Nat.find_min (exists_stop A hG K hr) hk)

lemma before_stop (hK : 0 < K) {r : ℝ} (hr : 0 < r) (Q : ℕ) (hQ : r ≤ A.S.a Q) :
    Q < stop A hG K r := by
  by_contra! h
  have ha := A.S.strictAnti.antitone h
  have hp : 1 < mast A (stop A hG K r) ^ K := one_lt_pow₀ (mast_gt_one A _) hK.ne'
  have hx := mul_lt_mul_of_pos_left hp (A.S.a_pos (stop A hG K r))
  rw [mul_one] at hx
  linarith [stop_spec A hG K hr]

lemma stop_tendsto (hK : 0 < K) : Tendsto (stop A hG K) (𝓝[>] (0 : ℝ)) atTop := by
  apply tendsto_atTop.mpr
  intro Q
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < A.S.a Q :=
    (eventually_lt_nhds (A.S.a_pos Q)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hQ
  exact (before_stop A hG K hK hr Q hQ.le).le

variable (paced : ∀ k, ((A.S.block k).val : ℝ) ≤ WilsonAdmissionScale.logarithm A k)
include paced

/-- Literal K/(K+1)-power native window at the same physical length. -/
theorem window (hK : 0 < K) {r : ℝ} (hr : 0 < r) (hsmall : r ≤ A.S.a 0) :
    A.S.a (stop A hG K r) * mast A (stop A hG K r) ^ K ≤ r ∧
      r ≤ A.S.a (stop A hG K r) * mast A (stop A hG K r) ^ (K + 1) := by
  refine ⟨stop_spec A hG K hr, ?_⟩
  let m := stop A hG K r
  have hm : 0 < m := before_stop A hG K hK hr 0 hsmall
  let j := m - 1
  have hj : j + 1 = m := by omega
  have hmin := stop_min A hG K hr (k := j) (by omega)
  have hstep : A.S.a j = A.S.a m * ((A.S.block j).val : ℝ) := by
    have hs := A.S.embeds_scale (A.S.oneStep j 0)
    change A.S.a (j + 1) * ((A.S.block j).val : ℝ) = A.S.a j at hs
    rw [hj] at hs
    exact hs.symm
  have hp : ((A.S.block j).val : ℝ) ≤ mast A m :=
    (paced j).trans ((WilsonAdmissionScale.logarithm_monotone A hG (show j ≤ m by omega)).trans (by dsimp only [mast]; linarith))
  have hl : mast A j ^ K ≤ mast A m ^ K :=
    pow_le_pow_left₀ (mast_pos A j).le (mast_monotone A hG (by omega)) K
  calc
    r ≤ A.S.a j * mast A j ^ K := hmin.le
    _ = A.S.a m * ((A.S.block j).val : ℝ) * mast A j ^ K := by rw [hstep]
    _ ≤ A.S.a m * mast A m * mast A m ^ K :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (A.S.a_pos m).le) hl
        (pow_nonneg (mast_pos A j).le _) (mul_nonneg (A.S.a_pos m).le (mast_pos A m).le)
    _ = A.S.a m * mast A m ^ (K + 1) := by rw [pow_succ]; ring

/-- The old Q bracket controls the exact overshoot into the admission stop. -/
theorem ratio_le (hK : 0 < K) {r : ℝ} (hr : 0 < r) (Q : ℕ)
    (hQ : r ≤ A.S.a Q) (hnext : A.S.a (Q + 1) < r) :
    A.S.a Q / A.S.a (stop A hG K r) ≤ mast A (stop A hG K r) ^ (K + 2) := by
  let m := stop A hG K r
  have hwindow := (window A hG K paced hK hr (hQ.trans (A.S.strictAnti.antitone (Nat.zero_le Q)))).2
  have hp : ((A.S.block Q).val : ℝ) ≤ mast A m :=
    (paced Q).trans ((WilsonAdmissionScale.logarithm_monotone A hG (before_stop A hG K hK hr Q hQ).le).trans (by dsimp only [mast]; linarith))
  have hstep : A.S.a Q = A.S.a (Q + 1) * ((A.S.block Q).val : ℝ) := by
    exact (A.S.embeds_scale (A.S.oneStep Q 0)).symm
  apply (div_le_iff₀ (A.S.a_pos m)).mpr
  calc
    A.S.a Q = A.S.a (Q + 1) * ((A.S.block Q).val : ℝ) := hstep
    _ ≤ r * ((A.S.block Q).val : ℝ) := mul_le_mul_of_nonneg_right hnext.le (Nat.cast_nonneg _)
    _ ≤ (A.S.a m * mast A m ^ (K + 1)) * mast A m :=
      mul_le_mul hwindow hp (Nat.cast_nonneg _) (mul_nonneg (A.S.a_pos m).le (pow_nonneg (mast_pos A m).le _))
    _ = mast A m ^ (K + 2) * A.S.a m := by simp only [pow_succ]; ring

variable {ι : Type} {l : Filter ι} {T ρ : ι → ℝ} {q : ι → ℕ}

omit hG paced in
private lemma height_from_log (hT : Tendsto T l atTop) (hρ : RateIs l T ρ (-1))
    (hq : Tendsto q l atTop)
    (hlog : Tendsto (fun i => Real.log (ρ i) / A.S.scale (q i)) l (𝓝 (-1))) :
    Height A.S l T q 1 := by
  have hsmall := (hρ.tends neg_one_lt_zero hT).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hh := hρ.rate.div hlog (show (-1 : ℝ) ≠ 0 by norm_num)
  norm_num only [neg_div_neg_eq, one_div_one] at hh
  refine ⟨hq, hh.congr' ?_⟩
  filter_upwards [hρ.pos, hsmall] with i hi hs
  have hn : Real.log (ρ i) ≠ 0 := (Real.log_neg hi hs).ne
  change (Real.log (ρ i) / T i) / (Real.log (ρ i) / A.S.scale (q i)) = A.S.scale (q i) / T i
  field_simp [hn]

/-- Native Height of the constructed finer stop; no inverse price premise. -/
theorem measured_stop_height (hK : 0 < K) (hT : Tendsto T l atTop) (hρ : RateIs l T ρ (-1)) :
    Height A.S l T (fun i => stop A hG K (ρ i)) 1 := by
  let m := fun i => stop A hG K (ρ i)
  have hρ0 : Tendsto ρ l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hρ.tends neg_one_lt_zero hT, hρ.pos⟩
  have hm : Tendsto m l atTop := (stop_tendsto A hG K hK).comp hρ0
  have hs := (A.S.divergent.comp hm).eventually_gt_atTop 0
  have hsmall := (hρ.tends neg_one_lt_zero hT).eventually (gt_mem_nhds (A.S.a_pos 0))
  have hMast := (WilsonAdmissionHeight.mast_log_rate A hG).comp hm
  have hlow : Tendsto
      (fun i => -1 + (K : ℝ) * (Real.log (WilsonMeasuredAdmission.mast A (m i)) / A.S.scale (m i)))
      l (𝓝 (-1)) := by simpa using (hMast.const_mul (K : ℝ)).const_add (-1)
  have hupp : Tendsto
      (fun i => -1 + ((K + 1 : ℕ) : ℝ) * (Real.log (WilsonMeasuredAdmission.mast A (m i)) / A.S.scale (m i)))
      l (𝓝 (-1)) := by simpa using (hMast.const_mul ((K + 1 : ℕ) : ℝ)).const_add (-1)
  apply height_from_log A hT hρ hm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [hρ.pos, hsmall, hs] with i hi hsmall hs
    change 0 < A.S.scale (m i) at hs
    have hw := (window A hG K paced hK hi hsmall.le).1
    have hp := Real.log_le_log (mul_pos (A.S.a_pos (m i))
      (pow_pos (WilsonMeasuredAdmission.mast_pos A (m i)) _)) hw
    rw [Real.log_mul (A.S.a_pos (m i)).ne'
      (pow_pos (WilsonMeasuredAdmission.mast_pos A (m i)) _).ne', Real.log_pow] at hp
    have ha : Real.log (A.S.a (m i)) = -A.S.scale (m i) := by simp [Schedule.scale]
    rw [ha] at hp
    have hd := div_le_div_of_nonneg_right hp hs.le
    simpa only [add_div, neg_div, div_self hs.ne', mul_div_assoc] using hd
  filter_upwards [hρ.pos, hsmall, hs] with i hi hsmall hs
  change 0 < A.S.scale (m i) at hs
  have hw := (window A hG K paced hK hi hsmall.le).2
  have hp := Real.log_le_log hi hw
  rw [Real.log_mul (A.S.a_pos (m i)).ne'
    (pow_pos (WilsonMeasuredAdmission.mast_pos A (m i)) _).ne', Real.log_pow] at hp
  have ha : Real.log (A.S.a (m i)) = -A.S.scale (m i) := by simp [Schedule.scale]
  rw [ha] at hp
  have hd := div_le_div_of_nonneg_right hp hs.le
  simpa only [add_div, neg_div, div_self hs.ne', mul_div_assoc] using hd

end YM.Integration.WilsonMeasuredWindow
