import YM.Integration.FVA1Physical.Round2.WindowSplit
import YM.RG.Bounded

/-! A common Haar rotation of the incoming configuration enforces the site gauge
symmetry while retaining the pointwise relative vacuum and numerator prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function Filter MeasureTheory Lattice Wilson RG
open scoped Classical
variable {G : Gauge} {n : Side} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def orbitMean (F : Config G n → E) (U : Config G n) :=
  ∫ z, F (gauge z U) ∂(Measure.pi fun _ : Site n => G.probHaar)

theorem orbitMean_gauge (F : Config G n → E) : GaugeInvariant (orbitMean F) := by
  intro z U
  let f := MeasurableEquiv.piCongrRight (fun i => MeasurableEquiv.mulRight (z i))
  let μ := Measure.pi fun _ : Site n => G.probHaar
  have hp : MeasurePreserving f μ μ := measurePreserving_pi _ _
    (fun i : Site n => measurePreserving_mul_right G.probHaar (z i))
  change (∫ v, F (gauge v (gauge z U)) ∂μ) = ∫ v, F (gauge v U) ∂μ
  rw [← hp.integral_comp' (fun v => F (gauge v U))]
  apply integral_congr_ae
  refine .of_forall fun v => congrArg F ?_
  funext i
  unfold Lattice.gauge
  change _ = (v _*z _)*U _*(v _*z _)⁻¹
  group

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

private theorem jointGauge : Measurable (fun a : Config G n × (Site n → G.El) => gauge a.2 a.1) := by
  refine measurable_pi_lambda _ fun i => ?_
  dsimp only [Lattice.gauge]; fun_prop

theorem orbitMean_meas {F : Config G n → E} (h : Measurable F) : Measurable (orbitMean F) :=
  ((h.comp jointGauge).stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi fun _ : Site n => G.probHaar)).measurable

omit [NormedSpace ℝ E] in
private theorem onOrbit {F : Config G n → E} (h : Envelope F) (U : Config G n) :
    Integrable (fun z => F (gauge z U)) (Measure.pi fun _ : Site n => G.probHaar) := by
  obtain ⟨C,b⟩ := h.cost
  exact Integrable.of_bound ((h.meas.comp jointGauge).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    C (.of_forall fun z => b (gauge z U))

theorem orbitMean_envelope {F : Config G n → E} (h : Envelope F) : Envelope (orbitMean F) := by
  obtain ⟨C,b⟩ := h.cost
  refine ⟨orbitMean_meas h.meas,C,fun U => ?_⟩
  unfold orbitMean
  calc
    _ ≤ ∫ _ : Site n → G.El, C ∂(Measure.pi fun _ : Site n => G.probHaar) :=
      norm_integral_le_of_norm_le (integrable_const C) (.of_forall fun z => b (gauge z U))
    _ = C := by simp

theorem orbitMean_pos {W : Config G n → ℝ} (hw : Envelope W) (pos : ∀ U, 0<W U) (U : Config G n) :
    0 < orbitMean W U := by
  apply (integral_pos_iff_support_of_nonneg (fun z => (pos (gauge z U)).le) (onOrbit hw U)).2
  rw [show Function.support (fun z => W (gauge z U)) = Set.univ from
    Set.eq_univ_of_forall fun z => (pos (gauge z U)).ne']
  simp

theorem orbitMean_distance [CompleteSpace E] {F H : Config G n → E} (hH : Envelope H) (symF : GaugeInvariant F)
    {D : Config G n → ℝ} (symD : GaugeInvariant D) {e : ℝ}
    (close : ∀ U, ‖F U-H U‖ ≤ e*D U) (U : Config G n) : ‖F U-orbitMean H U‖ ≤ e*D U := by
  let μ := Measure.pi fun _ : Site n => G.probHaar
  have eq : F U-orbitMean H U = ∫ z, F U-H (gauge z U) ∂μ := by
    rw [integral_sub (integrable_const _) (onOrbit hH U),integral_const,probReal_univ,one_smul]; rfl
  rw [eq]
  have point (z : Site n → G.El) : ‖F U-H (gauge z U)‖ ≤ e*D U := by
    simpa only [symF z U,symD z U] using close (gauge z U)
  simpa only [integral_const,probReal_univ,one_smul] using
    (norm_integral_le_of_norm_le (μ:=μ) (integrable_const (e*D U)) (.of_forall point))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem orbitMean_dominated {H : Config G n → E} {W : Config G n → ℝ} (hW : Envelope W) {M : ℝ}
    (b : ∀ U, ‖H U‖ ≤ M*W U) (U : Config G n) : ‖orbitMean H U‖ ≤ M*orbitMean W U := by
  simpa only [orbitMean,integral_const_mul] using norm_integral_le_of_norm_le
    ((onOrbit hW U).const_mul M) (.of_forall fun z => b (gauge z U))

end YM.Integration.FVA1Physical.Round2
