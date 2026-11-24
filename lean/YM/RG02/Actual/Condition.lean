import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.SectorTags
import YM.Push.BETA_TRANSPORT.Noise
import YM.Extra.MULTISOURCE_TRAJECTORIES.Signals
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Literal conditional measure at one physical step

Disintegrate with the coarse argument held fixed. The actual predictor draws
have likelihood with respect to *counting*, including branch decisions and
all repetitions and regardless of large fields. `joint` includes also the
Markov normalization with fixed fine field (i.e. the `StepData.penaltyZ`
inside `StepData.density`); for marked observables with coarse field held fixed
one still has to divide by `denominator` from the push with the full vacuum
fine density. Use with the same `History` on which the density is known.

No volume-uniform reciprocal or source-census norm bound here. Positivity,
measurability etc. do *not* presume any new comparison hypotheses.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG02.Conditional

open Filter Function Set MeasureTheory RG Wilson Lattice
open Push.BetaTransport Extra.Trajectories
open scoped YM.Push.LogIdentity.Tags Topology Matrix.Norms.Frobenius BigOperators ENNReal

variable {G : Gauge} {c f : Side} (S : StepData c f)

abbrev Scene (S : StepData c f) (G : Gauge) := Config G f × S.Choices

def reference (G : Gauge) := (prior G f).prod (Measure.count : Measure S.Choices)

instance : IsFiniteMeasure (reference S G) := by unfold reference; infer_instance

/-- The mark-independent factor in the integrand. Does not include the
fine vacuum, which may itself have a marked extension. -/
def gate (β : ℝ) (V : Config G c) (s : Scene S G) := tagWeight S β s.2 s.1 V

def joint (R : Rep G f) (V : Config G c) (s : Scene S G) : ℝ := gate S R.beta V s*R.eval s.1

@[simp] lemma gate_nonneg (β : ℝ) (V : Config G c) (s : Scene S G) : 0 ≤ gate S β V s := tagWeight_nonneg ..

lemma gate_envelope (h : S.patch.Branches S.kernel G) (β : ℝ) (V : Config G c) : Envelope (gate S β V) := by
  constructor
  · let g (i : S.Choices) (s : Scene S G) := if s.2=i then tagWeight S β i s.1 V else 0
    have ht (i : S.Choices) : Measurable (fun s : Scene S G => tagWeight S β i s.1 V) := by
      have hg := (tag_estimate S h i).measurable β
      change Measurable ((fun p : Config G f × Config G c => tagWeight S β i p.1 p.2) ∘ fun s : Scene S G => (s.1,V))
      exact hg.comp (show Measurable (fun s : Scene S G => (s.1,V)) from measurable_fst.prodMk measurable_const)
    have hp : gate S β V = fun s => ∑ i : S.Choices, g i s := funext fun s => by simp [gate,g]
    rw [hp]; apply Finset.measurable_fun_sum; intro i _
    exact Measurable.ite (p:=fun s : Scene S G => s.2=i) (measurable_snd (measurableSet_singleton i)) (ht i) measurable_const
  obtain ⟨C,H⟩ := S.density_bound h β
  refine ⟨C,fun ⟨U,t⟩ => ?_⟩
  rw [Real.norm_of_nonneg (gate_nonneg ..)]
  exact (Finset.single_le_sum (fun i (_ : i∈Finset.univ) => tagWeight_nonneg S i β U V)
    (Finset.mem_univ t)).trans (H U V)

lemma charge_envelope {R : Rep G f} {A L θ ε η : ℝ} (hR : R.Lawful A L θ ε η)
    (h : S.patch.Branches S.kernel G) (V : Config G c) : Envelope (joint S R V) := by
  unfold joint
  have hF := R.envelope hR
  refine Envelope.mul (gate_envelope S h _ _) ⟨?_,?_⟩
  · exact hF.meas.comp measurable_fst
  obtain ⟨C,hC⟩ := hF.cost
  exact ⟨C,fun i => hC _⟩

/-- Unmarked *field-dependent* denominator. -/
def denominator (R : Rep G f) (V : Config G c) := ∫ z, joint S R V z ∂reference S G

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Include `gate` in `w`. -/
theorem integrate (w : Scene S G → X) (h : Integrable w (reference S G)) :
    (∫ s,w s ∂reference S G)=∫ U,(∑ t:S.Choices,w (U,t)) ∂prior G f := by
  rw [reference,integral_prod w h]; simp only [MeasureTheory.integral_count]

omit [CompleteSpace X] in
theorem push_mark (F : Config G f → X) (hF : Integrable F (prior G f)) (V : Config G c) (β : ℝ)
    (h : S.patch.Branches S.kernel G) : Integrable (fun s : Scene S G => gate S β V s • F s.1) (reference S G) := by
  have he := gate_envelope S h β V
  obtain ⟨C,hC⟩ := he.cost
  exact (hF.comp_fst _).bdd_smul C he.meas.aestronglyMeasurable (Eventually.of_forall hC)

theorem common_gate (F : Config G f → X) (hF : Integrable F (prior G f)) (V : Config G c) (β : ℝ)
    (h : S.patch.Branches S.kernel G) :
    S.push β F V = ∫ s : Scene S G, gate S β V s • F s.1 ∂reference S G := by
  rw [integrate _ _ (push_mark S F hF V β h)]
  unfold StepData.push StepData.density
  simp only [Finset.sum_smul]; rfl

theorem denominator_value {R : Rep G f} {A L θ ε η : ℝ} (hR : R.Lawful A L θ ε η)
    (h : S.patch.Branches S.kernel G) (V : Config G c) :
    denominator S R V=S.push R.beta R.eval V :=
  (common_gate S R.eval ((R.envelope hR).integrable _) V R.beta h).symm

/-- Posterior with coarse field held fixed. Requires nonnegative input
and positive denominator. -/
def posterior (R : Rep G f) (V : Config G c) : Measure (Scene S G) :=
  (reference S G).withDensity fun s => ENNReal.ofReal ((denominator S R V)⁻¹ * joint S R V s)

section Hyp
variable {R : Rep G f} {A L θ ε η : ℝ} (hR : R.Lawful A L θ ε η)
    (hb : ∀ U, 0≤R.eval U) (h : S.patch.Branches S.kernel G)
    {V : Config G c} (hv : 0<denominator S R V)
include hb hv

lemma nonneg (s : Scene S G) : 0 ≤ (denominator S R V)⁻¹ * joint S R V s :=
  mul_nonneg (inv_pos.mpr hv).le (mul_nonneg (gate_nonneg ..) (hb s.1))
include hR h

theorem probability : IsProbabilityMeasure (posterior S R V) := by
  constructor
  rw [posterior, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_const_mul, ← denominator, inv_mul_cancel₀ hv.ne', ENNReal.ofReal_one]
  · exact ((charge_envelope S hR h V).integrable _).const_mul _
  exact Eventually.of_forall fun i => nonneg S hb hv i

omit [CompleteSpace X] in
lemma posterior_integrable (F : Scene S G → X) : Integrable F (posterior S R V) ↔
    Integrable ((fun s => joint S R V s • F s) : Scene S G → X) (reference S G) := by
  rw [posterior, integrable_withDensity_iff_integrable_smul' (by exact
    ((charge_envelope S hR h V).meas.const_mul _).ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (nonneg S hb hv _),mul_smul]
  exact integrable_fun_smul_iff (inv_ne_zero hv.ne') _

set_option linter.unusedSectionVars false in -- deliberately CompleteSpace, to interpret Bochner expectation
/-- Conditional-moment identification at the actual normalized law,
usable through each coefficient and its stored sets. -/
theorem posterior_expectation (F : Scene S G → X) (_ : Integrable F (posterior S R V)) :
    (∫ s, F s ∂posterior S R V) = (denominator S R V)⁻¹ • ∫ s,joint S R V s • F s ∂reference S G := by
  rw [posterior,integral_withDensity_eq_integral_toReal_smul (by exact
    ((charge_envelope S hR h V).meas.const_mul _).ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (nonneg S hb hv _),mul_smul,integral_smul]
end Hyp
end YM.RG02.Conditional
