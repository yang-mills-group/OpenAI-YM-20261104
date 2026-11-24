import YM.Integration.WilsonAdmissionScale

/-! A finer admission stop for the original bracketed physical length.
The fifth/sixth-power window is the literal numerical content of the native
RG05Readout `measured` convention. The original coarse Q is not replaced. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonMeasuredAdmission

open Filter Set
open scoped Topology

variable {G : Gauge} (A : RG.Levels G) (hG : G.Simple)

/-- Exactly the native RG05Readout logarithmic mast. -/
def mast (k : ℕ) : ℝ := 2 + WilsonAdmissionScale.logarithm A k

lemma mast_pos (k : ℕ) : 0 < mast A k := by
  have := WilsonAdmissionScale.logarithm_pos A k
  unfold mast
  linarith

lemma mast_gt_one (k : ℕ) : 1 < mast A k := by
  have := WilsonAdmissionScale.logarithm_pos A k
  unfold mast
  linarith

include hG

lemma mast_monotone : Monotone (mast A) :=
  fun _ _ h => add_le_add le_rfl (WilsonAdmissionScale.logarithm_monotone A hG h)

lemma weighted_mast_tendsto :
    Tendsto (fun k => A.S.a k * mast A k ^ 5) atTop (𝓝 0) := by
  have hlarge := (WilsonAdmissionScale.logarithm_tendsto A hG).eventually_ge_atTop 2
  have hzero := (WilsonAdmissionScale.weighted_spacing_tendsto A hG).const_mul 32
  rw [mul_zero] at hzero
  apply squeeze_zero' (.of_forall fun k => mul_nonneg (A.S.a_pos k).le (pow_nonneg (mast_pos A k).le _)) ?_ hzero
  filter_upwards [hlarge] with k hk
  have hpow : mast A k ^ 5 ≤ 32 * WilsonAdmissionScale.logarithm A k ^ 6 := by
    calc
      mast A k ^ 5 ≤ (2 * WilsonAdmissionScale.logarithm A k) ^ 5 :=
        pow_le_pow_left₀ (mast_pos A k).le (by dsimp only [mast]; linarith) 5
      _ = 32 * WilsonAdmissionScale.logarithm A k ^ 5 := by ring
      _ ≤ 32 * WilsonAdmissionScale.logarithm A k ^ 6 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (by decide)) (by norm_num)
  exact (mul_le_mul_of_nonneg_left hpow (A.S.a_pos k).le).trans_eq (by ring)

private lemma exists_stop {r : ℝ} (hr : 0 < r) :
    ∃ k : ℕ, A.S.a k * mast A k ^ 5 ≤ r :=
  ((weighted_mast_tendsto A hG).eventually (gt_mem_nhds hr)).exists.imp fun _ h => h.le

/-- Least stop meeting the native fifth-power window. Zero outside the
positive length domain is only a total-function convention. -/
def stop (r : ℝ) : ℕ := if hr : 0 < r then Nat.find (exists_stop A hG hr) else 0

lemma stop_spec {r : ℝ} (hr : 0 < r) :
    A.S.a (stop A hG r) * mast A (stop A hG r) ^ 5 ≤ r := by
  rw [stop, dif_pos hr]
  exact Nat.find_spec (exists_stop A hG hr)

private lemma stop_min {r : ℝ} (hr : 0 < r) {k : ℕ} (hk : k < stop A hG r) :
    r < A.S.a k * mast A k ^ 5 := by
  rw [stop, dif_pos hr] at hk
  exact lt_of_not_ge (Nat.find_min (exists_stop A hG hr) hk)

lemma before_stop {r : ℝ} (hr : 0 < r) (Q : ℕ) (hQ : r ≤ A.S.a Q) :
    Q < stop A hG r := by
  by_contra! h
  have ha := A.S.strictAnti.antitone h
  have hp : 1 < mast A (stop A hG r) ^ 5 := one_lt_pow₀ (mast_gt_one A _) (by decide)
  have hx := mul_lt_mul_of_pos_left hp (A.S.a_pos (stop A hG r))
  rw [mul_one] at hx
  linarith [stop_spec A hG hr]

lemma stop_tendsto : Tendsto (stop A hG) (𝓝[>] (0 : ℝ)) atTop := by
  apply tendsto_atTop.mpr
  intro Q
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < A.S.a Q :=
    (eventually_lt_nhds (A.S.a_pos Q)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hQ
  exact (before_stop A hG hr Q hQ.le).le

variable (paced : ∀ k, ((A.S.block k).val : ℝ) ≤ WilsonAdmissionScale.logarithm A k)
include paced

/-- Literal fifth/sixth-power native window at the same physical length. -/
theorem window {r : ℝ} (hr : 0 < r) (hsmall : r ≤ A.S.a 0) :
    A.S.a (stop A hG r) * mast A (stop A hG r) ^ 5 ≤ r ∧
      r ≤ A.S.a (stop A hG r) * mast A (stop A hG r) ^ 6 := by
  refine ⟨stop_spec A hG hr, ?_⟩
  let m := stop A hG r
  have hm : 0 < m := before_stop A hG hr 0 hsmall
  let j := m - 1
  have hj : j + 1 = m := by omega
  have hmin := stop_min A hG hr (k := j) (by omega)
  have hstep : A.S.a j = A.S.a m * ((A.S.block j).val : ℝ) := by
    have hs := A.S.embeds_scale (A.S.oneStep j 0)
    change A.S.a (j + 1) * ((A.S.block j).val : ℝ) = A.S.a j at hs
    rw [hj] at hs
    exact hs.symm
  have hp : ((A.S.block j).val : ℝ) ≤ mast A m :=
    (paced j).trans ((WilsonAdmissionScale.logarithm_monotone A hG (show j ≤ m by omega)).trans (by dsimp only [mast]; linarith))
  have hl : mast A j ^ 5 ≤ mast A m ^ 5 :=
    pow_le_pow_left₀ (mast_pos A j).le (mast_monotone A hG (by omega)) 5
  calc
    r ≤ A.S.a j * mast A j ^ 5 := hmin.le
    _ = A.S.a m * ((A.S.block j).val : ℝ) * mast A j ^ 5 := by rw [hstep]
    _ ≤ A.S.a m * mast A m * mast A m ^ 5 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (A.S.a_pos m).le) hl
        (pow_nonneg (mast_pos A j).le _) (mul_nonneg (A.S.a_pos m).le (mast_pos A m).le)
    _ = A.S.a m * mast A m ^ 6 := by ring

/-- The old Q bracket controls the exact overshoot into the admission stop. -/
theorem ratio_le {r : ℝ} (hr : 0 < r) (Q : ℕ)
    (hQ : r ≤ A.S.a Q) (hnext : A.S.a (Q + 1) < r) :
    A.S.a Q / A.S.a (stop A hG r) ≤ mast A (stop A hG r) ^ 7 := by
  let m := stop A hG r
  have hwindow := (window A hG paced hr (hQ.trans (A.S.strictAnti.antitone (Nat.zero_le Q)))).2
  have hp : ((A.S.block Q).val : ℝ) ≤ mast A m :=
    (paced Q).trans ((WilsonAdmissionScale.logarithm_monotone A hG (before_stop A hG hr Q hQ).le).trans (by dsimp only [mast]; linarith))
  have hstep : A.S.a Q = A.S.a (Q + 1) * ((A.S.block Q).val : ℝ) := by
    exact (A.S.embeds_scale (A.S.oneStep Q 0)).symm
  apply (div_le_iff₀ (A.S.a_pos m)).mpr
  calc
    A.S.a Q = A.S.a (Q + 1) * ((A.S.block Q).val : ℝ) := hstep
    _ ≤ r * ((A.S.block Q).val : ℝ) := mul_le_mul_of_nonneg_right hnext.le (Nat.cast_nonneg _)
    _ ≤ (A.S.a m * mast A m ^ 6) * mast A m :=
      mul_le_mul hwindow hp (Nat.cast_nonneg _) (mul_nonneg (A.S.a_pos m).le (pow_nonneg (mast_pos A m).le _))
    _ = mast A m ^ 7 * A.S.a m := by ring

/-- Any already purchased eighth-power room contains the unchanged Q. -/
theorem room_encloses {r : ℝ} (hr : 0 < r) (Q j : ℕ)
    (hQ : r ≤ A.S.a Q) (hnext : A.S.a (Q + 1) < r)
    (hlarge : 128 ≤ WilsonAdmissionScale.logarithm A (stop A hG r))
    (hroom : Push.GridApprox.room A j (stop A hG r)
      (Nat.ceil (WilsonAdmissionScale.logarithm A (stop A hG r) ^ 8))) : j ≤ Q := by
  let m := stop A hG r
  let L := WilsonAdmissionScale.logarithm A m
  have hpow : mast A m ^ 7 ≤ L ^ 8 := by
    calc
      mast A m ^ 7 ≤ (2 * L) ^ 7 :=
        pow_le_pow_left₀ (mast_pos A m).le (by dsimp only [mast]; change 2 + L ≤ 2 * L; linarith) 7
      _ = 128 * L ^ 7 := by ring
      _ ≤ L * L ^ 7 := mul_le_mul_of_nonneg_right hlarge (pow_nonneg (by linarith) _)
      _ = L ^ 8 := by ring
  have hu := (div_le_iff₀ (A.S.a_pos m)).mp (ratio_le A hG paced hr Q hQ hnext)
  have hx : A.S.a Q ≤ A.S.a m * L ^ 8 :=
    hu.trans ((mul_le_mul_of_nonneg_right hpow (A.S.a_pos m).le).trans_eq (mul_comm ..))
  have hceil := mul_le_mul_of_nonneg_left (Nat.le_ceil (L ^ 8)) (A.S.a_pos m).le
  by_contra! h
  have hanti := A.S.strictAnti h
  change 2 * (A.S.a m * (Nat.ceil (L ^ 8) : ℝ) + Push.GridApprox.tail A m) < A.S.a j at hroom
  have ht := Push.GridApprox.tail_pos A m
  have hn : 0 ≤ A.S.a m * L ^ 8 := mul_nonneg (A.S.a_pos m).le (pow_nonneg (by linarith) _)
  linarith


omit paced in
/-- The actual native squared budget becomes small before any choice of
body profiles, cutoff, period or replica family. -/
theorem fine_spacing {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      2 * A.S.a (stop A hG r) *
        (1 + ((A.budget (stop A hG r)).B : ℝ) ^ 2) < η * r := by
  have hmast : Tendsto (mast A) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (WilsonAdmissionScale.logarithm_tendsto A hG)
  have hlarge := (hmast.comp (stop_tendsto A hG)).eventually_gt_atTop (4 / η)
  filter_upwards [self_mem_nhdsWithin, hlarge] with r hr hlarge
  let m := stop A hG r
  let L := WilsonAdmissionScale.logarithm A m
  let t := mast A m
  have hL : 0 < L := WilsonAdmissionScale.logarithm_pos A m
  have ht : 1 < t := mast_gt_one A m
  have hB : ((A.budget m).B : ℝ) ≤ t ^ 2 := by
    have hb := (Nat.ceil_lt_add_one (sq_nonneg L)).le
    change ((Nat.ceil (L ^ 2) : ℕ) : ℝ) ≤ (2 + L) ^ 2
    nlinarith
  have hB2 := pow_le_pow_left₀ (Nat.cast_nonneg (A.budget m).B) hB 2
  have hfour : 1 ≤ t ^ 4 := one_le_pow₀ ht.le
  have hbound : 2 * (1 + ((A.budget m).B : ℝ) ^ 2) ≤ 4 * t ^ 4 := by nlinarith
  have hηt : 4 < η * t := by
    have hh := (div_lt_iff₀ hη).mp hlarge
    simpa only [Function.comp_apply, t, m, mul_comm] using hh
  have hcost : 4 * t ^ 4 < η * t ^ 5 := by
    have hh := mul_lt_mul_of_pos_right hηt (pow_pos (zero_lt_one.trans ht) 4)
    nlinarith
  have hs := stop_spec A hG hr
  calc
    2 * A.S.a m * (1 + ((A.budget m).B : ℝ) ^ 2) =
        A.S.a m * (2 * (1 + ((A.budget m).B : ℝ) ^ 2)) := by ring
    _ ≤ A.S.a m * (4 * t ^ 4) := mul_le_mul_of_nonneg_left hbound (A.S.a_pos m).le
    _ < A.S.a m * (η * t ^ 5) := mul_lt_mul_of_pos_left hcost (A.S.a_pos m)
    _ = η * (A.S.a m * t ^ 5) := by ring
    _ ≤ η * r := mul_le_mul_of_nonneg_left hs hη.le

/-- The enclosure threshold precedes every possible original-Q bracket
and every already purchased eighth-power room. -/
theorem rooms_eventually_enclose :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ Q j : ℕ,
      r ≤ A.S.a Q → A.S.a (Q + 1) < r →
      Push.GridApprox.room A j (stop A hG r)
        (Nat.ceil (WilsonAdmissionScale.logarithm A (stop A hG r) ^ 8)) → j ≤ Q := by
  have hlarge := ((WilsonAdmissionScale.logarithm_tendsto A hG).comp
    (stop_tendsto A hG)).eventually_ge_atTop 128
  filter_upwards [self_mem_nhdsWithin, hlarge] with r hr hlarge Q j hQ hnext hroom
  exact room_encloses A hG paced hr Q j hQ hnext hlarge hroom

end YM.Integration.WilsonMeasuredAdmission
