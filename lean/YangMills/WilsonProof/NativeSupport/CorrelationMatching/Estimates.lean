import YangMills.WilsonProof.NativeSupport.CorrelationMatching.CorrelationEquations
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Measurements
import YangMills.WilsonProof.NativeSupport.MeasuredShapeJets

set_option autoImplicit false
noncomputable section

namespace YangMills.CorrelationMatching

open Filter Matching
open scoped Topology ContDiff BigOperators Classical

variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}

def measuredCorrelation {B : Maxwell.Reference g} (H : Measurement B T)
    {n : ℕ} (phase : Option T.Character) (center : Spacetime)
    (fields : Fin n → Label B) (r : ℝ) (x : Points n) : ℂ :=
  T.correlation phase (H.inputs r fields) (WithLp.toLp 2 fun i => center + r • x i)

def truncation (g : GaugeGroup) (S : Conversion (maxwellReference g))
    {n : ℕ} (p : ℕ) (coupling : ℝ) (fields : Fin n → Label (maxwellReference g))
    (x : Points n) : ℂ :=
  ∑ k : Fin (p+1), (coupling : ℂ)^k.val * convertedCoefficient g S k.val fields x

/-- The three remainder estimates use the same coupling and field coordinates.
The phase estimate compares the mean and every vacuum with one another. The
last two clauses identify the series of the physical Ward stress. -/
structure Estimates (g : GaugeGroup) {C : WilsonFamily g} {T : Hierarchy C}
    (S : Conversion (maxwellReference g)) (H : Measurement (maxwellReference g) T) : Prop where
  tested (n : ℕ) (d : Fin n → ℕ) : ∃ m : ℕ,
    ∀ (phase : Option T.Character) (v : (i : Fin n) → (maxwellReference g).sector (d i))
      (center : Spacetime),
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      HasExpansion m H.coupling (measuredCorrelation H phase center fields)
        (fun k x => convertedCoefficient g S k fields x)
  compact (n p : ℕ) (d : Fin n → ℕ) (center : Spacetime) (K : Set (Points n)) :
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ phase : Option T.Character,
      ∀ (v : (i : Fin n) → (maxwellReference g).sector (d i)) (x : Points n), x ∈ K →
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      ‖measuredCorrelation H phase center fields r x - truncation g S p (H.coupling r) fields x‖ ≤
        A * (∏ i, sectorMass (v i)) * |H.coupling r|^(p+1)
  derivatives (n p j : ℕ) (d : Fin n → ℕ) (K : Set (Points n)) :
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (phase : Option T.Character)
      (v : (i : Fin n) → (maxwellReference g).sector (d i)) (center : Spacetime)
      (x : Points n), x ∈ K →
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      shapeJetEstimateAt j (measuredCorrelation H phase center fields r)
        (truncation g S p (H.coupling r) fields) x
        (A * (∏ i, sectorMass (v i)) * |H.coupling r|^(p+1))
  phaseAgreement (n j : ℕ) (d : Fin n → ℕ) (K : Set (Points n)) :
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∀ γ : ℝ, 0 < γ → γ < 4 → ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ (phase₁ phase₂ : Option T.Character) (center : Spacetime)
      (v : (i : Fin n) → (maxwellReference g).sector (d i)) (x : Points n), x ∈ K →
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      ‖iteratedFDeriv ℝ j (fun y =>
        measuredCorrelation H phase₁ center fields r y - measuredCorrelation H phase₂ center fields r y) x‖ ≤
        r ^ γ * ∏ i, sectorMass (v i)
  uniqueStress : ∃! P : WardStress.Series (maxwellReference g),
    WardIdentities g S P
  stressExpansion (P : WardStress.Series (maxwellReference g)) :
    WardIdentities g S P →
    ∀ (a b : Axis) (p : ℕ) (out : (maxwellReference g).sector 4 →ₗ[ℂ] ℂ),
      Tendsto (fun r : ℝ =>
        (out ((H.frame r 4).symm ((r : ℂ)^4 • T.stress a b)) -
          ∑ k : Fin (p+1), (H.coupling r : ℂ)^k.val * out (P k.val a b)) /
            (H.coupling r : ℂ)^p) (𝓝[>] 0) (𝓝 0)

end YangMills.CorrelationMatching
