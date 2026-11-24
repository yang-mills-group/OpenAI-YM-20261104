import YM.Integration.FVA1Physical.Wilson.MovingExterior

/-! A bounded signed source may see both the retained field and the full
history, and may vary with the coupling. Vacuum domination pays its entire
outside-chart contribution with the uniform exceptional-history estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set MeasureTheory Lattice RG YM.Wilson Tree Precision RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart
open scoped Classical Topology
variable {G : Gauge} {n c : Side} (d : Descent n c)

def pathAmplitude (β : ℕ → ℝ) (t : d.Tags) (J : Config G c → Fields G d → ℝ)
    (V : Config G c) (x : Fields G d) : ℝ :=
  d.probability t x * Real.exp (-d.account β t V x) * J V x

def pathRegion (g : ℝ) (a : ℕ → ℝ) (t : d.Tags) (J : Config G c → Fields G d → ℝ)
    (V : Config G c) (U : Set (Fields G d)) : ℝ :=
  (g^Module.finrank ℝ (Coordinates G d))⁻¹ *
    ∫ x in U, pathAmplitude d (offset a g) t J V x ∂d.measure G

theorem pathAmplitude_measurable (h : d.OK G) (β : ℕ → ℝ) (t : d.Tags)
    (J : Config G c → Fields G d → ℝ) (V : Config G c) (hj : Measurable (J V)) :
    Measurable (pathAmplitude d β t J V) :=
  ((prob_measurable h t).mul (Real.continuous_exp.measurable.comp
    (((account_envelope h β t).meas.comp (measurable_const.prodMk measurable_id)).neg))).mul hj

theorem pathAmplitude_le (β : ℕ → ℝ) (t : d.Tags)
    (J : Config G c → Fields G d → ℝ) (V : Config G c) (B : ℝ)
    (hb : ∀ x, ‖J V x‖ ≤ B) (x : Fields G d) :
    ‖pathAmplitude d β t J V x‖ ≤ d.integrand β t (fun _ => B) V x := by
  let q := d.probability t x * Real.exp (-d.account β t V x)
  have hq : 0 ≤ q := mul_nonneg (probability_nonneg ..) (Real.exp_pos _).le
  change ‖q * J V x‖ ≤ q * B
  rw [norm_mul,Real.norm_of_nonneg hq]
  exact mul_le_mul_of_nonneg_left (hb x) hq

theorem pathAmplitude_integrable (h : d.OK G) (β : ℕ → ℝ) (t : d.Tags)
    (J : Config G c → Fields G d → ℝ) (V : Config G c) (hj : Measurable (J V))
    {B : ℝ} (hb : ∀ x, ‖J V x‖ ≤ B) : Integrable (pathAmplitude d β t J V) (d.measure G) :=
  (path_integrable h β t (fun _ => B) continuous_const V).mono'
    (pathAmplitude_measurable d h β t J V hj).aestronglyMeasurable
    (Eventually.of_forall (pathAmplitude_le d β t J V B hb))

theorem path_exterior (h : d.Room G) (Z : ChartRatio G) (hZ : LocalRatio Z) {r : ℝ}
    (hr : 0 < r) (hs : r ≤ small G Z) (M B : ℝ) (hB : 0 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ, 0 < g →
      ∀ (a : ℕ → ℝ), d.Band M a → ∀ (V : Config G c), QuietLinks V ε →
      ∀ (t : d.Tags) (J : Config G c → Fields G d → ℝ), (∀ x, ‖J V x‖ ≤ B) →
        ‖pathRegion d g a t J V (chamber G d.Links r)ᶜ‖ ≤ C*g^k := by
  obtain ⟨ε,hε,H⟩ := moving_exterior d h Z hZ hr hs M B hB
  refine ⟨ε,hε,fun k => ?_⟩
  obtain ⟨C,hC,H⟩ := H k
  refine ⟨C,hC,fun g hg a ha V hv t J hJ => ?_⟩
  let U := (chamber G d.Links r)ᶜ
  have fee := H g hg a ha V hv t (fun _ => B) (fun _ => (Real.norm_of_nonneg hB).le)
  change ‖_ * _‖ ≤ _
  rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hg.le _))]
  calc
    _ ≤ movingRegion d g a t (fun _ => B) V U :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le
        ((path_integrable (room_ok d h) (offset a g) t (fun _ => B) continuous_const V).integrableOn)
        (Eventually.of_forall (pathAmplitude_le d _ t J V B hJ)))
        (inv_nonneg.mpr (pow_nonneg hg.le _))
    _ ≤ _ := (le_abs_self _).trans fee

end YM.Integration.FVA1Physical.Wilson
