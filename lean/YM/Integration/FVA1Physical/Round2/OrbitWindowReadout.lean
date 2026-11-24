import YM.Integration.FVA1Physical.Round2.WindowOrbit
import YM.Integration.FVA1Physical.Sources.Round2.PhysicalKernelLawful

/-! Average the independently computed field over just the eligible gauges.
The Haar mass can be arbitrarily small. The same mass occurs on both sides
of the integrated error and cancels exactly. The window is chosen before
the probes, field, perturbative coefficient, or real/imaginary reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Set Filter Finset MeasureTheory Lattice RG YM.Wilson Precision
open YM.Integration.FVA1Physical.Wilson MSbar MSbar.Mosaic MSbar.Bulk MSbar.Heath.Cottage
open RGComparison.Core16 RGComparison.Core16.Spool
open scoped Classical Topology
variable {G : Gauge} {c : Side}

private def rotations (G : Gauge) (c : Side) := Measure.pi fun _ : Site c => G.probHaar

private theorem rotate_cont (V : Config G c) : Continuous (fun z : Site c → G.El => gauge z V) := by
  apply continuous_pi
  intro i
  dsimp only [Lattice.gauge]
  fun_prop

def orbitWindow (B : Set (Config G c)) (Q : Config G c → ℝ) (V : Config G c) : ℝ :=
  orbitMean (B.indicator Q) V / orbitMean (B.indicator (fun _ => (1:ℝ))) V

theorem orbitWindow_gauge (B : Set (Config G c)) (Q : Config G c → ℝ) :
    GaugeInvariant (orbitWindow B Q) := by
  intro a V
  exact congrArg₂ (· / ·) (orbitMean_gauge _ a V) (orbitMean_gauge _ a V)

theorem orbitWindow_meas (B : Set (Config G c)) (hB : MeasurableSet B) {Q : Config G c → ℝ}
    (hQ : Measurable Q) : Measurable (orbitWindow B Q) :=
  (orbitMean_meas (hQ.indicator hB)).div (orbitMean_meas (measurable_const.indicator hB))

private theorem indicator_pull (B : Set (Config G c)) (Q : Config G c → ℝ) (V : Config G c) :
    (fun z : Site c → G.El => B.indicator Q (gauge z V)) =
      ((fun z => gauge z V) ⁻¹' B).indicator (fun z => Q (gauge z V)) := by
  funext z
  by_cases h : gauge z V ∈ B <;> simp [h]

theorem orbitWindow_price (B : Set (Config G c)) (hB : IsOpen B)
    (F Q : Config G c → ℝ) (sym : GaugeInvariant F) (hQ : Measurable Q)
    (V : Config G c) (a : Site c → G.El) (ha : gauge a V ∈ B) {e : ℝ}
    (bound : ∀ U ∈ B, |F U - Q U| ≤ e) : |F V - orbitWindow B Q V| ≤ e := by
  let μ := rotations G c
  haveI : IsProbabilityMeasure μ := by dsimp [μ,rotations]; infer_instance
  let E := (fun z : Site c → G.El => gauge z V) ⁻¹' B
  have hopen : IsOpen E := hB.preimage (rotate_cont V)
  have hpos : 0 < μ E := by
    haveI : μ.IsOpenPosMeasure := by dsimp [μ,rotations]; infer_instance
    exact Measure.measure_pos_of_mem_nhds μ (hopen.mem_nhds (show a ∈ E from ha))
  have hmass : 0 < μ.real E := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have point (z : Site c → G.El) (hz : z ∈ E) : |F V - Q (gauge z V)| ≤ e := by
    simpa only [sym z V] using bound (gauge z V) hz
  have core : ∀ᵐ z ∂μ.restrict E, |F V - Q (gauge z V)| ≤ e := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with z hz using point z hz
  have hq : Integrable (fun z : Site c → G.El => Q (gauge z V)) (μ.restrict E) := by
    apply Integrable.of_bound (hQ.comp (rotate_cont V).measurable).aestronglyMeasurable (|F V| + e)
    filter_upwards [core] with z hz
    rw [Real.norm_eq_abs]
    calc
      |Q (gauge z V)| = |F V - (F V - Q (gauge z V))| := by congr 1; ring
      _ ≤ |F V| + |F V - Q (gauge z V)| := abs_sub _ _
      _ ≤ _ := add_le_add le_rfl hz
  have price : ‖∫ z in E, F V - Q (gauge z V) ∂μ‖ ≤ μ.real E * e := by
    calc
      _ ≤ ∫ _ in E, e ∂μ := norm_integral_le_of_norm_le (integrable_const e) (by simpa only [Real.norm_eq_abs] using core)
      _ = _ := by rw [setIntegral_const,smul_eq_mul]
  have num : orbitMean (B.indicator Q) V = ∫ z in E, Q (gauge z V) ∂μ := by
    change (∫ z, B.indicator Q (gauge z V) ∂μ) = _
    rw [indicator_pull,integral_indicator hopen.measurableSet]
  have den : orbitMean (B.indicator (fun _ => (1:ℝ))) V = μ.real E := by
    change (∫ z, B.indicator (fun _=> (1:ℝ)) (gauge z V) ∂μ) = _
    rw [indicator_pull,integral_indicator hopen.measurableSet]
    rw [setIntegral_const,smul_eq_mul,mul_one]
  rw [integral_sub (integrable_const _) hq,setIntegral_const,smul_eq_mul,Real.norm_eq_abs] at price
  rw [orbitWindow,num,den,←mul_div_cancel_right₀ (F V) hmass.ne',←sub_div,abs_div,abs_of_pos hmass]
  exact (div_le_iff₀ hmass).mpr (by simpa only [mul_comm] using price)

end YM.Integration.FVA1Physical.Round2.Curvature
