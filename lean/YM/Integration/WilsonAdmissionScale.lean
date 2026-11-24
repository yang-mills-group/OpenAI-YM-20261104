import YM.Next.RANK.Station
import YM.Push.GRID_APPROXIMATION.Geometry

/-! A finer stop on the unchanged schedule. The pace inequality below is
exactly the existing `Flick.grade` receipt retained by the common Broad.
The stop is selected before physical positions, labels and fine cutoffs.
No initial marked representation or signed estimate is supplied here. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonAdmissionScale
open Filter Lattice RG
open scoped Topology Classical

variable {G : Gauge} (A : Levels G)

def logarithm (k : ℕ) : ℝ := Real.log (A.clock.hatBeta k)

lemma logarithm_pos (k : ℕ) : 0 < logarithm A k :=
  Real.log_pos (A.fits.delayed k)

lemma logarithm_monotone (hG : G.Simple) : Monotone (logarithm A) := by
  have hs : Monotone A.S.scale := monotone_nat_of_le_succ fun k => by
    rw [Schedule.scale_succ]
    exact le_add_of_nonneg_right (Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ (A.S.block k).val from (A.S.block k).property)))
  intro i j hij
  apply Real.log_le_log (zero_lt_one.trans (A.fits.delayed i))
  change A.clock.bar + G.slopeConstant * A.S.scale i ≤ A.clock.bar + G.slopeConstant * A.S.scale j
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hs hij)
    (Gauge.slopeConstant_pos hG).le)

lemma logarithm_tendsto (hG : G.Simple) :
    Tendsto (logarithm A) atTop atTop :=
  Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate A hG)

/-- A fixed logarithmic mesh reserve still tends to zero on this schedule. -/
theorem weighted_spacing_tendsto (hG : G.Simple) :
    Tendsto (fun k => A.S.a k * logarithm A k ^ 6) atTop (𝓝 0) := by
  have hlog := (Real.tendsto_log_atTop.comp (logarithm_tendsto A hG)).eventually_ge_atTop 6
  have hupper : ∀ᶠ k in atTop,
      A.S.a k * logarithm A k ^ 6 ≤ Next.Rank.Station.gap A 1 k := by
    filter_upwards [hlog] with k hk
    apply mul_le_mul_of_nonneg_left ?_ (A.S.a_pos k).le
    change logarithm A k ^ 6 ≤ A.clock.monitor k ^ (1 : ℝ)
    rw [Real.rpow_one]
    have he : logarithm A k ^ 6 = Real.exp (6 * Real.log (logarithm A k)) := by
      simpa only [Nat.cast_ofNat, Real.exp_log (logarithm_pos A k)] using
        (Real.exp_nat_mul (Real.log (logarithm A k)) 6).symm
    rw [he]
    apply Real.exp_le_exp.mpr
    change 6 * Real.log (logarithm A k) ≤ Real.log (logarithm A k) ^ 2
    change 6 ≤ Real.log (logarithm A k) at hk
    nlinarith
  exact squeeze_zero' (Eventually.of_forall fun k =>
    mul_nonneg (A.S.a_pos k).le (pow_nonneg (logarithm_pos A k).le _))
    hupper (Next.Rank.Station.gap_rate A hG 1)

private lemma exists_stop (hG : G.Simple) (Q : ℕ) :
    ∃ m, A.S.a m * logarithm A m ^ 6 ≤ A.S.a Q :=
  ((weighted_spacing_tendsto A hG).eventually (ge_mem_nhds (A.S.a_pos Q))).exists

/-- The first stop paying the fixed six-logarithm reserve, on the original
schedule and relative to the original paid Q. -/
def stop (hG : G.Simple) (Q : ℕ) : ℕ := Nat.find (exists_stop A hG Q)

lemma stop_spec (hG : G.Simple) (Q : ℕ) :
    A.S.a (stop A hG Q) * logarithm A (stop A hG Q) ^ 6 ≤ A.S.a Q :=
  Nat.find_spec (exists_stop A hG Q)

variable (hG : G.Simple)
    (paced : ∀ k, ((A.S.block k).val : ℝ) ≤ logarithm A k)
include paced

private lemma logarithm_three (k : ℕ) : 3 ≤ logarithm A k :=
  (by exact_mod_cast A.S.block_large k : (3 : ℝ) ≤ (A.S.block k).val).trans (paced k)

/-- Every selected stop is strictly finer than its unchanged paid Q. -/
theorem before_stop (Q : ℕ) : Q < stop A hG Q := by
  by_contra! h
  have ha := A.S.strictAnti.antitone h
  have hp : 1 < logarithm A (stop A hG Q) ^ 6 :=
    one_lt_pow₀ (by have := logarithm_three A paced (stop A hG Q); linarith) (by decide)
  have ht : A.S.a (stop A hG Q) <
      A.S.a (stop A hG Q) * logarithm A (stop A hG Q) ^ 6 := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hp (A.S.a_pos (stop A hG Q))
  exact (not_lt_of_ge (stop_spec A hG Q)) (ha.trans_lt ht)

/-- The first-crossing overshoot costs only one additional logarithm,
using the actual retained pace inequality. -/
theorem stop_ratio (Q : ℕ) :
    logarithm A (stop A hG Q) ^ 6 ≤ A.S.a Q / A.S.a (stop A hG Q) ∧
      A.S.a Q / A.S.a (stop A hG Q) ≤ logarithm A (stop A hG Q) ^ 7 := by
  let m := stop A hG Q
  have hm : 0 < m := (Nat.zero_le Q).trans_lt (before_stop A hG paced Q)
  have hlow : logarithm A m ^ 6 ≤ A.S.a Q / A.S.a m :=
    (le_div_iff₀ (A.S.a_pos m)).mpr (by simpa only [mul_comm] using stop_spec A hG Q)
  refine ⟨hlow, ?_⟩
  let j := m - 1
  have hj : j < m := Nat.sub_lt hm Nat.zero_lt_one
  have hnext : j + 1 = m := Nat.sub_add_cancel hm
  have hprev : A.S.a Q < A.S.a j * logarithm A j ^ 6 :=
    lt_of_not_ge (Nat.find_min (exists_stop A hG Q) hj)
  have he : A.S.a m * ((A.S.block j).val : ℝ) = A.S.a j := by
    have h := A.S.embeds_scale (A.S.oneStep j 0)
    simpa only [Schedule.oneStep, hnext] using h
  have hmono := logarithm_monotone A hG hj.le
  apply le_of_lt
  calc
    A.S.a Q / A.S.a m <
        (A.S.a m * ((A.S.block j).val : ℝ) * logarithm A j ^ 6) / A.S.a m := by
      rw [he]
      exact (div_lt_div_iff_of_pos_right (A.S.a_pos m)).mpr hprev
    _ = ((A.S.block j).val : ℝ) * logarithm A j ^ 6 := by field_simp [(A.S.a_pos m).ne']
    _ ≤ logarithm A m * logarithm A m ^ 6 :=
      mul_le_mul ((paced j).trans hmono)
        (pow_le_pow_left₀ (logarithm_pos A j).le hmono 6)
        (pow_nonneg (logarithm_pos A j).le _) (logarithm_pos A m).le
    _ = logarithm A m ^ 7 := by ring

lemma stop_tendsto : Tendsto (stop A hG) atTop atTop :=
  tendsto_atTop_mono (fun Q => (before_stop A hG paced Q).le) tendsto_id


/-- Any native room with its existing eighth-power radius starts before
the original Q. Thus the purchased corridor contains the new stop and Q. -/
theorem room_encloses (Q j : ℕ)
    (hroom : Push.GridApprox.room A j (stop A hG Q)
      (Nat.ceil (logarithm A (stop A hG Q) ^ 8))) : j ≤ Q := by
  let m := stop A hG Q
  have hl : 3 ≤ logarithm A m := logarithm_three A paced m
  have hpow : logarithm A m ^ 7 ≤ logarithm A m ^ 8 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  have hceil : logarithm A m ^ 8 ≤ (Nat.ceil (logarithm A m ^ 8) : ℝ) := Nat.le_ceil _
  have hupper : A.S.a Q ≤ A.S.a m * logarithm A m ^ 7 := by
    have hu := (div_le_iff₀ (A.S.a_pos m)).mp (stop_ratio A hG paced Q).2
    simpa only [mul_comm] using hu
  by_contra! h
  have hanti := A.S.strictAnti h
  change 2 * (A.S.a m * (Nat.ceil (logarithm A m ^ 8) : ℝ) +
    Push.GridApprox.tail A m) < A.S.a j at hroom
  have h₁ := mul_le_mul_of_nonneg_left hpow (A.S.a_pos m).le
  have h₂ := mul_le_mul_of_nonneg_left hceil (A.S.a_pos m).le
  have ht := Push.GridApprox.tail_pos A m
  have hn : 0 ≤ A.S.a m * logarithm A m ^ 7 :=
    mul_nonneg (A.S.a_pos m).le (pow_nonneg (logarithm_pos A m).le _)
  linarith

/-- The actual squared native cover radius is small compared with the
physical radius, uniformly in every radius using the original Q bracket. -/
theorem native_radius_small {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∀ᶠ Q : ℕ in atTop, ∀ r : ℝ, 0 ≤ r →
      A.S.a (Q + 1) < 8 * r * (M + 1) →
      A.S.a (stop A hG Q) *
        (((A.budget (stop A hG Q)).B : ℝ) ^ 2 + 3) ≤ η * r / 2 := by
  have hlarge := ((logarithm_tendsto A hG).comp (stop_tendsto A hG paced)).eventually_ge_atTop
    (80 * (M + 1) / η)
  filter_upwards [hlarge] with Q hlarge r hr hbracket
  let m := stop A hG Q
  let t := logarithm A m
  have ht : 0 < t := logarithm_pos A m
  have ht3 : 3 ≤ t := logarithm_three A paced m
  have hb : ((A.budget m).B : ℝ) ≤ t ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (sq_nonneg t)).le
  have hb' : ((A.budget m).B : ℝ) ≤ 2 * t ^ 2 := by nlinarith
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (A.budget m).B) hb' 2
  have hfour := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) ht3 4
  have hB : ((A.budget m).B : ℝ) ^ 2 + 3 ≤ 5 * t ^ 4 := by
    norm_num at hfour
    nlinarith
  have hstep : A.S.a (Q + 1) * ((A.S.block Q).val : ℝ) = A.S.a Q := by
    simpa only [Schedule.oneStep] using A.S.embeds_scale (A.S.oneStep Q 0)
  have hp : ((A.S.block Q).val : ℝ) ≤ t :=
    (paced Q).trans (logarithm_monotone A hG (before_stop A hG paced Q).le)
  have hsmall : A.S.a m * t ^ 6 ≤ 8 * r * (M + 1) * t := by
    apply (stop_spec A hG Q).trans
    calc
      A.S.a Q = A.S.a (Q + 1) * ((A.S.block Q).val : ℝ) := hstep.symm
      _ ≤ 8 * r * (M + 1) * ((A.S.block Q).val : ℝ) :=
        mul_le_mul_of_nonneg_right hbracket.le (Nat.cast_nonneg _)
      _ ≤ 8 * r * (M + 1) * t := mul_le_mul_of_nonneg_left hp (by positivity)
  have hηt : 80 * (M + 1) ≤ η * t := by
    have hh := (div_le_iff₀ hη).mp hlarge
    simpa only [Function.comp_apply, t, m, mul_comm] using hh
  calc
    A.S.a m * (((A.budget m).B : ℝ) ^ 2 + 3) ≤ A.S.a m * (5 * t ^ 4) :=
      mul_le_mul_of_nonneg_left hB (A.S.a_pos m).le
    _ = 5 * (A.S.a m * t ^ 6) / t ^ 2 := by field_simp [ht.ne']
    _ ≤ 5 * (8 * r * (M + 1) * t) / t ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall (by norm_num)) (sq_nonneg t)
    _ = 40 * r * (M + 1) / t := by field_simp [ht.ne']; ring
    _ ≤ η * r / 2 := by
      apply (div_le_iff₀ ht).mpr
      have hh := mul_le_mul_of_nonneg_left hηt hr
      nlinarith

omit paced in
/-- Every Q obeying the original upper bracket is late when r is small;
no replacement of the already selected Q is needed. -/
theorem fitting_scales_late (q : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ Q : ℕ,
      A.S.a (Q + 1) < 8 * r * (M + 1) → q ≤ Q := by
  have hden : 0 < 8 * (M + 1) := by positivity
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < A.S.a q / (8 * (M + 1)) :=
    (eventually_lt_nhds (div_pos (A.S.a_pos q) hden)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall] with r hr Q hQ
  by_contra! h
  have ha := A.S.strictAnti.antitone (show Q + 1 ≤ q by omega)
  have hh := (lt_div_iff₀ hden).mp hr
  nlinarith

end YM.Integration.WilsonAdmissionScale
