import YM.MatchingR2.Top.Back
import YM.SectorNext.VACUUM_NORMALIZATION.Noise

/-!
# Gap under the step kernel (in powers of `t` = inverse bare coupling g)

All tags retained even over all coarse fields. Use shell lower bound at one wire only (Qualit.
integrability at each torus ok from fixed-volume envelope).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingR2.Top
open RG Function Wilson Lattice MeasureTheory Filter Set Finset Tree Push.SectorMeasure Pressure SectorNext.Vacuum
open scoped Topology BigOperators ContDiff ENNReal Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio) (β : ℝ) (o : Site c)
set_option quotPrecheck false
local notation "t₀" => Real.sqrt β
local notation "Fine" => Config G f
local notation "Coarse" => Config G c
local notation "σ" => S.kernel.penalty
local notation "Z₀" => S.penaltyZ β G
local notation "π₀" => prior G c
local notation "π₁" => prior G f

lemma deposit (u : G.El) : (∫ v, (Z₀)⁻¹ * S.penaltyWeight β (v * u⁻¹) ∂G.probHaar) = 1 := by
  rw [integral_const_mul,
    (measurePreserving_mul_right G.probHaar u⁻¹).integral_comp ((Homeomorph.mulRight u⁻¹).measurableEmbedding) (S.penaltyWeight β)]
  exact inv_mul_cancel₀ (S.penaltyZ_pos _).ne'
variable (p : ℕ)
local notation "C₀" => shellBill G S β

def quartile (G : Gauge) := Real.sqrt (2*(shellBill G S β+(p:ℝ)*Real.log t₀)/σ)
def collected (G : Gauge) := quartile S β p G ^ p + 2^p

lemma weight_power (hβ : 1 ≤ β) :
    ∫ u : G.El, (Z₀)⁻¹ * S.penaltyWeight β u * (t₀*G.chord u)^p ∂G.probHaar ≤ collected S β p G := by
  let r := quartile S β p G
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have ht : 1 ≤ t₀ := Real.one_le_sqrt.mpr hβ
  have hx : 0 < t₀ := zero_lt_one.trans_le ht
  have hl : Real.log (4*(1+|β|)) ≥ 0 := Real.log_nonneg (by linarith [abs_nonneg β])
  have hv : 0 < σ := S.kernel.penalty_pos
  have hb : 0 ≤ C₀ := by unfold shellBill; positivity
  have hP : r^2 = 2*(C₀+(p:ℝ)*Real.log t₀)/σ := Real.sq_sqrt (by positivity [Real.log_nonneg ht])
  let M (u:G.El) := (Z₀)⁻¹ * S.penaltyWeight β u
  let N (u:G.El) := t₀ * G.chord u
  have hM (u) : 0 ≤ M u := mul_nonneg (inv_nonneg.mpr (S.penaltyZ_pos _).le) (Real.exp_pos _).le
  have hN (u) : 0 ≤ N u := mul_nonneg hx.le (G.chord_nonneg _)
  have hQ u (he:r ≤ N u) : M u ≤ t₀⁻¹ ^ p := by
    unfold M StepData.penaltyWeight
    have hn : (Z₀)⁻¹ ≤ Real.exp C₀ := by
      simpa only [Real.exp_neg,inv_inv] using (inv_anti₀ (Real.exp_pos _) (pZ_lo S (G:=G) β))
    apply le_trans (mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le)
    rw [← Real.exp_add, ← Real.exp_log (inv_pos.mpr hx), Real.log_inv, ← Real.exp_nat_mul]
    apply Real.exp_monotone
    have hh : r^2 ≤ N u ^2 := pow_le_pow_left₀ hr he 2
    rw [hP, div_le_iff₀ hv] at hh; unfold N at hh; rw [mul_pow,G.chord_price, Real.sq_sqrt (zero_le_one.trans hβ)] at hh
    linarith only [hh]
  have hall u : M u * N u^p ≤ M u * r^p + 2^p := by
    rcases le_total (N u) r with h|h
    · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hN _) h p) (hM u)).trans (le_add_of_nonneg_right (by positivity))
    refine le_add_of_nonneg_of_le (mul_nonneg (hM u) (pow_nonneg hr _)) ?_
    calc
      _ ≤ t₀⁻¹ ^p * (t₀ * 2)^p := mul_le_mul (hQ u h) (pow_le_pow_left₀ (hN u) (mul_le_mul_of_nonneg_left (G.chord_le_two _) hx.le) _) (pow_nonneg (hN u) _) (by positivity)
      _ = _ := by rw [← mul_pow, inv_mul_cancel_left₀ hx.ne']
  have hmc : Continuous M := continuous_const.mul (S.penaltyWeight_cont β)
  have hi (g : G.El→ℝ) (h: Continuous g) : Integrable g G.probHaar := h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpay : ∫ u, M u ∂G.probHaar=1 := by unfold M; rw [integral_const_mul]; exact inv_mul_cancel₀ (S.penaltyZ_pos _).ne'
  change (∫ u,M u*N u^p ∂G.probHaar) ≤ _
  apply (integral_mono (hi _ (hmc.mul ((continuous_const.mul G.continuous_chord).pow _)))
    (((hi _ hmc).mul_const (r^p)).add (integrable_const _)) hall).trans_eq
  simp only [Pi.add_apply]
  rw [integral_add ((hi _ hmc).mul_const _) (integrable_const _), integral_mul_const,hpay,integral_const]
  simp [r,collected]

lemma noise_power (Q : Coarse) (e : Edge (Site c)) :
    ∫ V, S.noise β Q V * (t₀*wire Q V e)^p ∂π₀ =
    ∫ u : G.El, (Z₀)⁻¹ * S.penaltyWeight β u * (t₀*G.chord u)^p ∂G.probHaar := by
  let M (i : Edge (Site c)) (v : G.El) := (Z₀)⁻¹ * S.penaltyWeight β (v*(Q i)⁻¹)
  let N (i : Edge (Site c)) (v : G.El) := M i v*(if i=e then (t₀*G.chord (v*(Q e)⁻¹))^p else 1)
  have he V : S.noise β Q V * (t₀*wire Q V e)^p = ∏ i, N i (V i) := by
    simp only [StepData.noise,wire,N,M,Finset.prod_mul_distrib]
    simp
  have hm i : (∫ v, M i v ∂G.probHaar)=1 := deposit S β _
  simp_rw [he]; unfold Wilson.prior
  rw [integral_fintype_prod_eq_prod N, Finset.prod_eq_single_of_mem e (mem_univ _)]
  · simp only [N,M,if_true]
    exact (measurePreserving_mul_right G.probHaar (Q e)⁻¹).integral_comp
      ((Homeomorph.mulRight (Q e)⁻¹).measurableEmbedding) (fun u : G.El=> (Z₀)⁻¹ * S.penaltyWeight β u * (t₀*G.chord u)^p)
  intro i hi hh; simp [N,hh, hm i]

variable (e : Edge (Site c))
def gap (j : S.Choices) (U : Fine) (V : Coarse) := t₀*wire (S.prediction U j) V e
def slack := pullRead (G:=G) S F o (gap S β e)
variable (H : S.patch.Branches S.kernel G)
include H
lemma gap_env (j) : Envelope (uncurry (gap (G:=G) S β e j)) := by
  let W (x : Coarse × Coarse) := t₀*wire x.1 x.2 e
  have hw : Continuous W := by unfold W wire; fun_prop
  change Envelope (W ∘ fun x : Fine × Coarse => (S.prediction x.1 j,x.2))
  exact envelope_comp (envelope_cart _ hw)
    (show Measurable (fun x : Fine × Coarse => (S.prediction x.1 j,x.2)) from ((S.prediction_meas H j).comp measurable_fst).prodMk measurable_snd)
lemma slack_env : Envelope (slack (G:=G) S F β o e) := pulledReadBound S F o (gap_env S β e H)
omit H in
lemma gap_pos (j) (U:Fine) (V:Coarse) : 0 ≤ gap S β e j U V := mul_nonneg (Real.sqrt_nonneg _) (G.chord_nonneg _)
omit H in
lemma slack_pos (x : All S F G) : 0 ≤ slack S F β o e x := gap_pos ..
lemma gap_power : ∫ x, slack S F β o e x ^ p ∂full S F β o G =
    ∫ u : G.El, (Z₀)⁻¹ * S.penaltyWeight β u * (t₀*G.chord u)^p ∂G.probHaar := by
  let M := ∫ u : G.El, (Z₀)⁻¹ * S.penaltyWeight β u * (t₀*G.chord u)^p ∂G.probHaar
  let A (j:S.Choices) (U:Fine) (V:Coarse) := gap S β e j U V ^ p
  have he i U : ∫ V : Coarse, ticket S β i U V * A i U V ∂π₀ = fineWeight β U * S.likelihood U i * M := by
    unfold A gap ticket tagged M; rw [← noise_power S β p (S.prediction U i) e, ← integral_const_mul]
    congr 1; ext1 V; ring
  have hf i : Covariant S (A i) := by
    intro t U V; unfold A gap; rw [(choice_gauge H U i t).2, wire_gauge]
  have ht : ∀ j, Envelope (uncurry (A j)) := fun j => envelope_pow (gap_env S β e H j) _
  change ∫ x, pullRead S F o A x ∂full S F β o G = _
  rw [cov_income S F β o H ht hf]
  simp_rw [he, integral_mul_const]
  have hu := (fine_weight_env (f:=f) (G:=G) β).integrable π₁
  rw [← Finset.sum_mul, ← integral_finsetSum _]
  · simp_rw [← Finset.mul_sum, S.chosen H, mul_one]; unfold fineWeight; rw [integral_div]; change partition G f β / _ * _ = _; rw [div_self (partition_pos _).ne', one_mul]
  intro i _; apply hu.mul_bdd (c:=1) (S.likelihood_meas H i).aestronglyMeasurable
  filter_upwards with U
  rw [Real.norm_of_nonneg (S.likelihood_pos ..)]; exact
    (Finset.single_le_sum (f:=fun j=> S.likelihood U j) (fun _ _=>S.likelihood_pos ..) (mem_univ i)).trans_eq (S.chosen H U)

end YM.MatchingR2.Top
