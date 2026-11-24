import YM.Integration.FVA1Physical.Wilson.LogTilt
import YM.Integration.FVA1Physical.Wilson.ForestAverageData
import YM.MSbar.Cottage.Suns

/-! Conditional forest laws with an independently supplied interior energy.
The denominator is an angular integral on the very same orbit as the numerator. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Lattice RG YM.Wilson Tree MSbar MSbar.Heath MSbar.Heath.Cottage
open scoped Classical Topology
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (F : Forest S.ratio) (I : Finset F.Free) (A : Set (Config G f))
variable (C φ : Config G f → ℝ)
local notation "K" => twirl F I
local notation "Ω" => IV F I G
local notation "μ" => fence F I G

def angleMass (f' : Config G f → ℝ) (U : Config G f) := ∫ t : Ω, f' (K t U) ∂μ
def ink (A : Set (Config G f)) (C : Config G f → ℝ) := fun U=> spec A U*Real.exp (C U)
def angularLaw (U : Config G f) :=
  spec A U * (angleMass F I (fun V=>ink A C V*φ V) U / angleMass F I (ink A C) U)

lemma angle_mass_invariant (f' : Config G f → ℝ) (t : Ω) (U : Config G f) :
    angleMass F I f' (K t U)=angleMass F I f' U := by
  unfold angleMass; simp_rw [ends]
  exact (climber F I G t).integral_comp (Homeomorph.mulRight t).measurableEmbedding (fun a : Ω=> f' (K a U))

lemma resample_normalized :
    Rota.resample F I (fun U=>ink A C U/angleMass F I (ink A C) U) A φ = angularLaw F I A C φ := by
  funext U
  unfold Rota.resample Rota.ghat angularLaw
  simp_rw [angle_mass_invariant,div_mul_eq_mul_div]
  rw [integral_const_mul,integral_div]
  rfl

theorem angle_mass_meas {v : Config G f → ℝ} (h : Measurable v) : Measurable (angleMass F I v) := by
  have rot : Measurable (fun a : Config G f × Ω => K a.2 a.1) :=
    ((twirlD F I G).comp (continuous_snd.prodMk continuous_fst)).measurable
  exact ((h.comp rot).stronglyMeasurable.integral_prod_right' (ν:=fence F I G)).measurable

theorem angular_law_meas (hot : MeasurableSet A) (hC : Measurable C) (hφ : Measurable φ) :
    Measurable (angularLaw F I A C φ) := by
  have hs : Measurable (spec A : Config G f → ℝ) := measurable_const.indicator hot
  have hz : Measurable (ink A C) := hs.mul (Real.measurable_exp.comp hC)
  exact hs.mul ((angle_mass_meas F I (hz.mul hφ)).div (angle_mass_meas F I hz))

lemma angle_law_restricted (U : Config G f) (live : U ∈ A) (ha : MeasurableSet A) :
    angularLaw F I A C φ U = patchMean ((fence F I G).restrict ((fun t : Ω => K t U) ⁻¹' A))
      (fun t=>Real.exp (C (K t U))) (fun t=>φ (K t U)) := by
  let D := (fun t : Ω=> K t U) ⁻¹' A
  have hD : MeasurableSet D := ha.preimage (((twirlD F I G).comp (continuous_id.prodMk continuous_const)).measurable)
  let mask : Ω→ℝ := D.indicator (fun _=>1)
  have units (t:Ω) : spec A (K t U)=mask t := by
    by_cases ht:t∈D
    · exact (Set.indicator_of_mem (show K t U∈A from ht) _).trans (Set.indicator_of_mem ht (fun _ : Ω => (1:ℝ))).symm
    exact (Set.indicator_of_notMem (show K t U∉A from ht) _).trans (Set.indicator_of_notMem ht (fun _ : Ω => (1:ℝ))).symm
  have id (v : Ω→ℝ) : (fun t=>mask t*v t)=D.indicator v := by
    funext t; by_cases ht:t∈D
    · rw [show mask t=1 from Set.indicator_of_mem ht _,Set.indicator_of_mem ht _,one_mul]
    rw [show mask t=0 from Set.indicator_of_notMem ht _,Set.indicator_of_notMem ht _,zero_mul]
  unfold angularLaw angleMass ink patchMean
  rw [show spec A U=1 from Set.indicator_of_mem live _,one_mul]
  simp_rw [units,mul_assoc]
  rw [id,id,integral_indicator hD,integral_indicator hD,smul_eq_mul,div_eq_inv_mul]
  rfl

/-- The independently normalized inner forest law is stable in both signs of the
tested observable. Its local mass can be arbitrarily small. -/
theorem angular_tilt {T P φ : Config G f → ℝ} (ha : MeasurableSet A) (tbound : Envelope T)
    (mP : Measurable P) (test : Measurable φ) {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (bound : ∀ V, |φ V| ≤ b)
    (osc : ∀ U, U∈A → ∀ t : Ω, K t U∈A →
      |(T (K t U)-P (K t U))-(T U-P U)| ≤ δ) (U : Config G f) :
    |angularLaw F I A T φ U-angularLaw F I A P φ U| ≤ (Real.exp (2*δ)-1)*b := by
  have cash : 0 ≤ (Real.exp (2*δ)-1)*b := mul_nonneg
    (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg zero_le_two hδ))) hb
  by_cases live : U∈A
  swap
  · simp only [angularLaw,show spec A U=0 from Set.indicator_of_notMem live _,zero_mul,sub_self,abs_zero]
    exact cash
  let k := fun t : Ω=> K t U
  let D := k ⁻¹' A
  let ν := (fence F I G).restrict D
  have mk : Measurable k := ((twirlD F I G).comp (continuous_id.prodMk continuous_const)).measurable
  have hD : MeasurableSet D := ha.preimage mk
  rw [angle_law_restricted F I A T φ U live ha,angle_law_restricted F I A P φ U live ha]
  by_cases empty : ν Set.univ=0
  · have hz : ν=0 := Measure.measure_univ_eq_zero.mp empty
    change |patchMean ν _ _-patchMean ν _ _| ≤ _
    rw [hz]; simp only [patchMean,integral_zero_measure,inv_zero,zero_smul,sub_self,abs_zero]
    exact cash
  have ib : Integrable (fun t:Ω=>(1:ℝ)*Real.exp (T (k t))) ν := by
    simpa only [one_mul,Function.comp_apply,Function.comp_def] using (backdrop tbound.exp mk).integrable ν
  have priced := log_tilt (fun _:Ω=>(1:ℝ)) (fun t=>Real.exp (T (k t))) (fun t=>P (k t)) ν
    (pos_iff_ne_zero.mpr empty) (fun _=>zero_lt_one) (fun _=>Real.exp_pos _) measurable_const ib
    ((mP.comp mk).aemeasurable) (T U-P U) δ hδ ?_ (fun t=>φ (k t))
    ((test.comp mk).aestronglyMeasurable) hb (Eventually.of_forall fun t=>bound (k t))
  · simpa only [one_mul,Real.norm_eq_abs] using priced
  filter_upwards [ae_restrict_mem hD] with t ht
  rw [Real.log_exp]
  exact osc U live t ht
end YM.Integration.FVA1Physical.Wilson
