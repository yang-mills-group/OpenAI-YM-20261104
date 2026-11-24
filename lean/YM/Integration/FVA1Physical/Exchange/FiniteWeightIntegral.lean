import YM.Integration.FVA1Physical.Exchange.FiniteResidualTilt

/-! The coefficientwise posterior denominator and numerator are the ordinary
integrals of one explicit finite polynomial in the signed residual. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.FVA1Physical.FibreMeasure
open MeasureTheory Filter
open scoped BigOperators
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

def weightJet (m : ℕ) (u : ℝ) : ℝ := 1+∑ j ∈ Finset.range m,tiltCoeff j*u^(j+1)

theorem finite_weight_integrals (μ : Measure X) [IsProbabilityMeasure μ] (m : ℕ) (e : X→ℝ)
    (powers : ∀ j<m, Integrable (fun y => (e y)^(j+1)) μ) (F : X→E)
    (fm : AEStronglyMeasurable F μ) (unit : ∀ᵐ y ∂μ,‖F y‖≤1) :
    (∫ y,weightJet m (e y) ∂μ) = vacuumJet m (fun j => ∫ y,(e y)^(j+1) ∂μ) ∧
    (∫ y,weightJet m (e y) • F y ∂μ) = readerJet m (∫ y,F y ∂μ)
      (fun j => ∫ y,(e y)^(j+1) • F y ∂μ) := by
  have h (j : ℕ) (hj : j ∈ Finset.range m) :
      Integrable (fun y => tiltCoeff j*(e y)^(j+1)) μ := (powers j (Finset.mem_range.mp hj)).const_mul _
  have fInt : Integrable F μ := (integrable_const 1).mono' fm unit
  have marked (j : ℕ) (hj : j ∈ Finset.range m) :
      Integrable (fun y => tiltCoeff j • ((e y)^(j+1) • F y)) μ :=
    ((powers j (Finset.mem_range.mp hj)).smul_bdd 1 fm unit).smul _
  constructor
  · simp only [weightJet,vacuumJet,integral_add (integrable_const _) (integrable_finsetSum _ h),
      integral_const,probReal_univ,one_smul,integral_finsetSum _ h,integral_const_mul]
  simp only [weightJet,readerJet,add_smul,one_smul,Finset.sum_smul,mul_smul,
    integral_add fInt (integrable_finsetSum _ marked),integral_finsetSum _ marked,integral_smul]

end YM.Integration.FVA1Physical.FibreMeasure
