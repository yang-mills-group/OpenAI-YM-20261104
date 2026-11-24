import YM.Integration.WilsonLocalKernelPairing
import YM.Push.SECTOR_MEASURE.Decompose
import YM.Push.GRID_APPROXIMATION.Bounds

/-! Signed and positive carriers on the exact observed links of a Wilson step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.RetainedWilsonConditional

open Function Finset Set MeasureTheory Lattice Wilson RG
open WilsonKernelCoupling Push.SectorMeasure.Env
open scoped BigOperators Topology Classical

variable {G : Gauge} {c f : Side} (S : StepData c f)
variable (A : Finset (Edge (Site c)))

/-- Cost of changing the coupling on the observed links at a single step. -/
def distortion (b a : ℝ) : ℝ := (Real.exp (2 * change S b a))^A.card

theorem distortion_pos (b a : ℝ) : 0 < distortion S A b a := pow_pos (Real.exp_pos _) _

private theorem distortion_symm (b a : ℝ) : distortion S A a b = distortion S A b a := by
  unfold distortion
  rw [change_symm S a b]

private theorem at_zero (h : S.patch.Branches S.kernel G) (U : Config G f) (x : A → G.El) :
    WilsonKernelCoupling.marginal S A 0 U x = 1 := by
  have hp (q v : G.El) : link S 0 q v = 1 := by simp [link,StepData.penaltyWeight,StepData.penaltyZ]
  simpa only [WilsonKernelCoupling.marginal,hp,prod_const_one,mul_one] using S.chosen h U

private theorem nonnegative (b : ℝ) (U : Config G f) (x : A → G.El) :
    0 ≤ WilsonKernelCoupling.marginal S A b U x :=
  sum_nonneg fun t _ => mul_nonneg (S.likelihood_pos U t) (prod_nonneg fun i _ => (link_pos S b (S.prediction U t i.val) (x i)).le)

/-- The retained likelihood has a joint bounded Borel density in the complete
fine Wilson field and all the observed coarse links. -/
theorem likelihood (h : S.patch.Branches S.kernel G) (b : ℝ) :
    Envelope (fun q : Config G f × (A → G.El) => WilsonKernelCoupling.marginal S A b q.1 q.2) := by
  refine ⟨?_,distortion S A b 0,fun q => ?_⟩
  · apply Finset.measurable_sum
    intro t _
    apply ((S.likelihood_meas h t).comp measurable_fst).mul
    apply Finset.measurable_prod
    intro i _
    have hq : Measurable fun q : Config G f × (A → G.El) => S.prediction q.1 t i.val :=
      (measurable_pi_apply i.val).comp ((S.prediction_meas h t).comp measurable_fst)
    have hx : Measurable fun q : Config G f × (A → G.El) => q.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    exact ((S.penaltyWeight_cont b).measurable.comp (hx.mul hq.inv)).div_const _
  rw [Real.norm_of_nonneg (nonnegative S A b q.1 q.2)]
  have hp := marginal_le S A b 0 q.1 q.2
  rw [at_zero S A h,mul_one] at hp
  exact hp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The signed carrier integrates the original retained likelihood against
its input section over the entire fine Haar field. -/
def carrier (b : ℝ) (g : Config G f → E) (x : A → G.El) : E :=
  ∫ U, WilsonKernelCoupling.marginal S A b U x • g U ∂prior G f

def posterior (b : ℝ) (w : Config G f → ℝ) (g : Config G f → E) (x : A → G.El) : E :=
  (carrier S A b w x)⁻¹ • carrier S A b g x

section Borel
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- All observed configurations have a measurable retained carrier. -/
theorem carrier_env (h : S.patch.Branches S.kernel G) (b : ℝ) {g : Config G f → E} (hg : Envelope g) :
    Envelope (carrier S A b g) :=
  Push.SectorMeasure.Env.marginal (scale (likelihood S A h b)
    (hg.comp_env (measurable_fst (β:=A → G.El)))) (prior G f)

end Borel

private theorem slice (h : S.patch.Branches S.kernel G) (b : ℝ) (x : A → G.El)
    {g : Config G f → E} (hg : Integrable g (prior G f)) :
    Integrable (fun U => WilsonKernelCoupling.marginal S A b U x • g U) (prior G f) := by
  apply smul_L1 (H := fun U => WilsonKernelCoupling.marginal S A b U x) _ hg
  exact (likelihood S A h b).comp_env (g := fun U : Config G f => (U,x)) (measurable_id.prodMk measurable_const)

theorem vacuum_order (h : S.patch.Branches S.kernel G) (b a : ℝ)
    {w : Config G f → ℝ} (hw : Integrable w (prior G f)) (hw₀ : ∀ U, 0 ≤ w U) (x : A → G.El) :
    carrier S A b w x ≤ distortion S A b a * carrier S A a w x := by
  unfold carrier
  rw [←integral_const_mul]
  apply integral_mono (slice S A h b x hw) ((slice S A h a x hw).const_mul _)
  intro U
  simp only [smul_eq_mul,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (marginal_le S A b a U x) (hw₀ U)

/-- The finite original fine mass bounds the retained Wilson denominator
above and below, charging only the observed links. -/
theorem vacuum_bounds (h : S.patch.Branches S.kernel G) (b : ℝ)
    {w : Config G f → ℝ} (hw : Integrable w (prior G f)) (hw₀ : ∀ U, 0 ≤ w U) (x : A → G.El) :
    (∫ U, w U ∂prior G f)/distortion S A b 0 ≤ carrier S A b w x ∧
    carrier S A b w x ≤ distortion S A b 0*(∫ U, w U ∂prior G f) := by
  have hz : carrier S A 0 w x = ∫ U, w U ∂prior G f := by simp only [carrier,at_zero S A h,one_smul]
  have hlo := vacuum_order S A h 0 b hw hw₀ x
  have hup := vacuum_order S A h b 0 hw hw₀ x
  rw [hz,distortion_symm S A b 0] at hlo
  rw [hz] at hup
  exact ⟨(div_le_iff₀ (distortion_pos S A _ _)).2 (by simpa only [mul_comm] using hlo),hup⟩

/-- Taking absolute value leaves the original fine weight inside the same
observed likelihood. -/
theorem signed_price (b : ℝ) (g : Config G f → E) (x : A → G.El) :
    ‖carrier S A b g x‖ ≤ carrier S A b (fun U => ‖g U‖) x := by
  unfold carrier
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact ae_of_all _ fun U => by
    change ‖WilsonKernelCoupling.marginal S A b U x • g U‖ = WilsonKernelCoupling.marginal S A b U x * ‖g U‖
    rw [norm_smul,Real.norm_of_nonneg (nonnegative S A b U x)]

/-- The two original retained likelihoods compare an actual signed carrier
with its positive mark under the comparison coupling. Both normalizing
vacua are integrated against the same fine weight. -/
theorem normalized_price (h : S.patch.Branches S.kernel G) (b a : ℝ)
    {w : Config G f → ℝ} (hw : Integrable w (prior G f)) (hw₀ : ∀ U, 0 ≤ w U)
    (hpos : 0 < ∫ U, w U ∂prior G f) {g : Config G f → E} (hg : Integrable g (prior G f)) (x : A → G.El) :
    ‖posterior S A b w g x‖ ≤ (distortion S A b a)^2 *
      (carrier S A a (fun U => ‖g U‖) x / carrier S A a w x) := by
  let k := distortion S A b a
  have hk : 0 < k := distortion_pos S A b a
  have hden (q : ℝ) : 0 < carrier S A q w x := (div_pos hpos (distortion_pos S A q 0)).trans_le
    (vacuum_bounds S A h q hw hw₀ x).1
  have hq := (signed_price S A b g x).trans (vacuum_order S A h b a hg.norm (fun _ => norm_nonneg _) x)
  have hd := vacuum_order S A h a b hw hw₀ x
  rw [distortion_symm S A b a] at hd
  have hi : 1 / carrier S A b w x ≤ k / carrier S A a w x :=
    (div_le_div_iff₀ (hden b) (hden a)).2 (by simpa only [one_mul] using hd)
  rw [posterior,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (hden b).le),←one_div]
  calc
    _ ≤ (k / carrier S A a w x) * (k * carrier S A a (fun U => ‖g U‖) x) :=
      mul_le_mul hi hq (norm_nonneg _) (div_nonneg hk.le (hden a).le)
    _ = _ := by dsimp only [k]; ring

end YM.Integration.RetainedWilsonConditional
