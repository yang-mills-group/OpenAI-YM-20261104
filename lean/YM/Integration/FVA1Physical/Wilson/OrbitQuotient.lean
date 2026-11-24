import YM.Integration.FVA1Physical.Wilson.OrbitBank
import YM.Integration.FVA1Physical.Wilson.ChartEnvelope
import YM.Integration.FVA1Physical.Wilson.OrbitCalibration
import YM.Integration.FVA1Physical.Wilson.HotelTest

/-! The independently computed interior expectation descends to the exterior
orbit. The measured law of its rejected interior points is charged separately. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk SectorNext.Vacuum
open scoped Classical Topology
variable {G : Gauge} {c f : Side} {Q : StepData c f} {R : Rep G f} {out : Rep G c}
variable (F : Forest Q.ratio) (I : Finset F.Free) (A : Set (Config G f))
variable (C φ : Config G f → ℝ)
local notation "κ" => twirl F I
local notation "Ω" => IV F I G
local notation "μ" => fence F I G

def orbitQuotient (U : Config G f) :=
  angleMass F I (fun V=>ink A C V*φ V) U / angleMass F I (ink A C) U

theorem orbitQuotient_invariant (t : Ω) (U : Config G f) :
    orbitQuotient F I A C φ (κ t U)=orbitQuotient F I A C φ U := by
  unfold orbitQuotient
  rw [angle_mass_invariant,angle_mass_invariant]

lemma angularLaw_indicator : angularLaw F I A C φ=A.indicator (orbitQuotient F I A C φ) := by
  funext U
  by_cases h:U∈A
  · rw [angularLaw,show spec A U=1 from Set.indicator_of_mem h _,one_mul,Set.indicator_of_mem h _]; rfl
  rw [angularLaw,show spec A U=0 from Set.indicator_of_notMem h _,zero_mul,Set.indicator_of_notMem h _]

lemma orbitQuotient_envelope (ha : MeasurableSet A) (hC : Envelope C) (hf : Measurable φ)
    {b : ℝ} (hb : 0 ≤ b) (hφ : ∀ U, |φ U| ≤ b) :
    Measurable (orbitQuotient F I A C φ) ∧ ∀ U, |orbitQuotient F I A C φ U| ≤ b := by
  have mask : Envelope (spec A) := Envelope.piece ha (Envelope.const 1) (Envelope.const 0)
  have weight : Envelope (ink A C) := mask.mul hC.exp
  refine ⟨(angle_mass_meas F I (weight.meas.mul hf)).div (angle_mass_meas F I weight.meas),?_⟩
  intro U
  let k := fun t : Ω=>κ t U
  let G' := fun t : Ω=> ink A C (k t)
  have mk : Measurable k := ((twirlD F I G).comp (continuous_id.prodMk continuous_const)).measurable
  have iG : Integrable G' μ := (backdrop weight mk).integrable _
  have pos (t:Ω) : 0 ≤ G' t := mul_nonneg (Set.indicator_nonneg (fun _ _=>zero_le_one) _) (Real.exp_pos _).le
  let D := ∫ t, G' t ∂μ
  have hD : 0 ≤ D := integral_nonneg pos
  change |(∫ t, G' t*φ (k t) ∂μ)/D| ≤ b
  by_cases zero : D=0
  · simp only [zero,div_zero,abs_zero]; exact hb
  rw [abs_div,abs_of_nonneg hD,div_le_iff₀ (lt_of_le_of_ne hD (Ne.symm zero))]
  have cap := norm_integral_le_of_norm_le (iG.mul_const b) (Eventually.of_forall fun t=>by
    rw [norm_mul,Real.norm_of_nonneg (pos t)]; exact mul_le_mul_of_nonneg_left (hφ (k t)) (pos t) :
    ∀ᵐ t ∂μ, ‖G' t*φ (k t)‖≤G' t*b)
  rw [integral_mul_const,Real.norm_eq_abs] at cap
  exact cap.trans_eq (mul_comm D b)

variable (W : ForestCell Q R out)
local notation "O" => represent (tint G (Exterior.Body 1 c) W.x)
local notation "area" => hotel W.F W.X W.Y W.J O W.center W.a W.b
local notation "copy" => chambers W.F W.Y W.J O W.center

lemma interiorEnergy_envelope {σ C δ Λ w g : ℝ} (law : R.Lawful σ C Λ δ w)
    (rentalBound : Envelope (rental W.F W.J R W.Y W.source O W.center))
    (B : Positions (Primary f G) → ℝ) (cont : Continuous B) :
    Envelope (interiorEnergy Q O W.source copy R.beta g B) := by
  have mc := (informed W.F W.X W.Y W.J O W.center W.voice W.posture.extendsX).1
  have hP := backdrop (chartLog_envelope (G:=G) (f:=f) g cont) mc
  have hR := backdrop (R.exponentEnv law) mc
  have eq : interiorEnergy Q O W.source copy R.beta g B =
    fun U=> (B (chartLog g (copy U)) + (-R.exponent (copy U))) + (rental W.F W.J R W.Y W.source O W.center U) := by
    funext U; unfold interiorEnergy rental; ring
  rw [eq]
  exact (hP.add hR.neg).add rentalBound
end YM.Integration.FVA1Physical.Wilson
