import YM.Integration.WilsonMatrixOriginalRealFields

/-! Individual real readings of the original positive Wilson covariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalSignedReading
open Function Filter MeasureTheory Table Spec Lattice RG Wilson RGComparison.Core16
open PhysicalNext.Repeat.Legato Next.UVStress Extraction Extraction.Order Push.GridApprox OPE OPE.Therm
open WilsonInvariantActionIntegratedPair WilsonInvariantActionPairMarginals WilsonMatrixOriginalRealFields
open private product from YM.Integration.WilsonInvariantActionIntegratedPair
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {N p u : ℕ}

def amount (χ : ℂ →L[ℝ] ℝ) (a b : R.family.label 4) (x : Fin 2 → Site (R.family.side N p)) : ℝ :=
  let μ := scene R.family.path N p N
  let A := fun U => (R.family.O N p a (x 0) U).re
  let B := fun U => χ (R.family.O N p b (x 1) U)
  (∫ U, A U * B U ∂μ) - (∫ U, A U ∂μ) * (∫ U, B U ∂μ)

private theorem read_covariance {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : X → ℝ) (B : X → ℂ) (χ : ℂ →L[ℝ] ℝ)
    (both : Integrable (fun U => A U • B U) μ) (second : Integrable B μ) :
    χ ((∫ U, (A U : ℂ) * B U ∂μ) - (∫ U, (A U : ℂ) ∂μ) * (∫ U, B U ∂μ)) =
      (∫ U, A U * χ (B U) ∂μ) - (∫ U, A U ∂μ) * (∫ U, χ (B U) ∂μ) := by
  rw [map_sub,integral_complex_ofReal]
  change χ (∫ U, A U • B U ∂μ) - χ ((∫ U, A U ∂μ) • (∫ U, B U ∂μ)) = _
  rw [←χ.integral_comp_comm both,χ.map_smul,χ.integral_comp_comm second]
  simp only [map_smul,smul_eq_mul]

theorem site (T : Slices R.family.path.levels p) (h : u ≤ N)
    (hn : R.family.ref 4 ≤ N) (a b : R.family.label 4) (χ : ℂ →L[ℝ] ℝ)
    (x : Fin 2 → Site (R.family.side N p)) :
    χ (posterior R T h (realLabel a) b x) = amount R χ a b x := by
  letI : IsProbabilityMeasure (scene R.family.path N p N) := probability R.makes.wilson le_rfl
  let A := fun U => (R.family.O N p a (x 0) U).re
  let B := R.family.O N p b (x 1)
  have ha : Continuous A := Complex.continuous_re.comp (R.family.continuousO ..)
  have hb : Continuous B := R.family.continuousO ..
  rw [WilsonInvariantActionIntegratedPair.finite,product,WilsonInvariantActionPairMarginals.marginal,
    WilsonInvariantActionPairMarginals.marginal]
  simp_rw [real_at a hn]
  exact read_covariance _ A B χ ((ha.smul hb).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (hb.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

def signed (a b : R.family.label 4) (χ : ℂ →L[ℝ] ℝ) (φ : Test 2) (N p : ℕ) : ℝ :=
  R.family.S.a N ^ (4*2) * ∑ x : Fin 2 → Site (R.family.side N p),
    (φ (cells R.family N p x)).re * amount R χ a b x

private theorem read_weight (χ : ℂ →L[ℝ] ℝ) (t : ℝ) (z : ℂ) :
    χ ((t : ℂ) * z) = t * χ z := χ.map_smul t z

theorem measured (cut : (N p : ℕ) → Fin (N+1)) (a b : R.family.label 4)
    (χ : ℂ →L[ℝ] ℝ) (φ : Test 2) (real_test : ∀ x, φ x = ((φ x).re : ℂ))
    (hn : R.family.ref 4 ≤ N) :
    χ (profile R cut (realLabel a) b φ N p) = signed R a b χ φ N p := by
  unfold profile signed
  rw [←Complex.ofReal_pow,read_weight,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  conv_lhs => rw [real_test (cells R.family N p x),read_weight]
  rw [site R _ _ hn]

end YM.Integration.WilsonMatrixOriginalSignedReading
