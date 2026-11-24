import YangMills.PerturbativeMatching.Reference
import YangMills.PerturbativeMatching.Measurement
import YangMills.PerturbativeMatching.Asymptotics

/-! The Wilson correlation functions in the measured frame and their converted MS-bar expansion. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.PerturbativeMatching

open Filter Matching
open scoped Topology ContDiff BigOperators Classical

variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}

def measuredCorrelation {B : Maxwell.Reference g} (measurement : Measurement B T)
    {n : ℕ} (phase : Option T.Character) (center : Spacetime)
    (fields : Fin n → Label B) (r : ℝ) (x : Points n) : ℂ :=
  T.correlation phase (measurement.inputs r fields) (WithLp.toLp 2 fun i => center + r • x i)

def correlationPartialSum (reference : Reference g)
    {n : ℕ} (order : ℕ) (coupling : ℝ) (fields : Fin n → Label (maxwellReference g))
    (x : Points n) : ℂ :=
  ∑ k : Fin (order + 1),
    (coupling : ℂ)^k.val * reference.scheme.conversion.correlation reference.coefficients k.val fields x

/-- The three remainder estimates use the same coupling and field coordinates.
The phase estimate compares the mean and every vacuum with one another. The
stress estimate identifies the physical stress with the unique Ward series. -/
structure CorrelationExpansion (reference : Reference g)
    (measurement : Measurement (maxwellReference g) T) : Prop where
  smeared (n : ℕ) (d : Fin n → ℕ) : ∃ m : ℕ,
    ∀ (phase : Option T.Character) (v : (i : Fin n) → (maxwellReference g).sector (d i))
      (center : Spacetime),
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      HasSmearedExpansion m measurement.coupling (measuredCorrelation measurement phase center fields)
        (fun k x => reference.scheme.conversion.correlation reference.coefficients k fields x)
  uniformOnCompact (n order : ℕ) (d : Fin n → ℕ) (center : Spacetime) (K : Set (Points n)) :
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ phase : Option T.Character,
      ∀ (v : (i : Fin n) → (maxwellReference g).sector (d i)) (x : Points n), x ∈ K →
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      ‖measuredCorrelation measurement phase center fields r x -
        correlationPartialSum reference order (measurement.coupling r) fields x‖ ≤
        A * (∏ i, coefficientNorm (v i)) * |measurement.coupling r|^(order + 1)
  shapeDerivatives (n order derivativeOrder : ℕ) (d : Fin n → ℕ) (K : Set (Points n)) :
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (phase : Option T.Character)
      (v : (i : Fin n) → (maxwellReference g).sector (d i)) (center : Spacetime)
      (x : Points n), x ∈ K →
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      ShapeDerivativeBound derivativeOrder (measuredCorrelation measurement phase center fields r)
        (correlationPartialSum reference order (measurement.coupling r) fields) x
        (A * (∏ i, coefficientNorm (v i)) * |measurement.coupling r|^(order + 1))
  phaseAgreement (n derivativeOrder : ℕ) (d : Fin n → ℕ) (K : Set (Points n)) :
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∀ γ : ℝ, 0 < γ → γ < 4 → ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ (phase₁ phase₂ : Option T.Character) (center : Spacetime)
      (v : (i : Fin n) → (maxwellReference g).sector (d i)) (x : Points n), x ∈ K →
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      ‖iteratedFDeriv ℝ derivativeOrder (fun y =>
        measuredCorrelation measurement phase₁ center fields r y - measuredCorrelation measurement phase₂ center fields r y) x‖ ≤
        r ^ γ * ∏ i, coefficientNorm (v i)
  stressExpansion (P : WardStress.Series (maxwellReference g)) :
    WardStress.Determined reference.coefficients reference.scheme.conversion P →
    ∀ (a b : Axis) (order : ℕ) (out : (maxwellReference g).sector 4 →ₗ[ℂ] ℂ),
      Tendsto (fun r : ℝ =>
        (out ((measurement.frame r 4).symm ((r : ℂ)^4 • T.stress a b)) -
          ∑ k : Fin (order + 1), (measurement.coupling r : ℂ)^k.val * out (P k.val a b)) /
            (measurement.coupling r : ℂ)^order) (𝓝[>] 0) (𝓝 0)

end YangMills.PerturbativeMatching
