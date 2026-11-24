import YangMills.WilsonProof.NativeSupport.SeparatedCorrelationBounds

/-! Short-distance separation of phases on the actual appointed fields. -/
set_option autoImplicit false
noncomputable section

namespace YangMills.Matching

open Filter Set
open scoped BigOperators Topology ContDiff

variable {g : GaugeGroup} {B : Maxwell.Reference g}
variable {C : WilsonFamily g} {T : Hierarchy C}

/-- Compare phases of one returned hierarchy at the same measured radius and
physical center. Derivatives are taken in the dimensionless separated
configuration. The Wilson mean is the value at `none`. -/
def phaseDifference (H : Measurement B T) {n : ℕ} (s : ℝ) (o : Spacetime)
    (a : Fin n → Label B) (p q : Option T.Character) (x : Points n) : ℂ :=
  let position : Points n := WithLp.toLp 2 fun i => o + s • x i
  T.correlation p (H.inputs s a) position - T.correlation q (H.inputs s a) position

/-- The same radius event controls every character, the Wilson mean, all
centers, all input fields and the indicated spatial derivatives. The returned
hierarchy, the finite input caps, the compact and the exponent are fixed first. -/
def PhaseProximity (H : Measurement B T) : Prop :=
  ∀ (n j : ℕ) (d : Fin n → ℕ) (K : Set (Points n)),
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∀ γ : ℝ, 0 < γ → γ < 4 → ∀ᶠ s : ℝ in 𝓝[>] 0,
    ∀ (p q : Option T.Character) (o : Spacetime)
        (v : (i : Fin n) → B.sector (d i)) (x : Points n), x ∈ K →
      ‖iteratedFDeriv ℝ j (phaseDifference H s o (fun i => ⟨d i, v i⟩) p q) x‖ ≤
        s ^ γ * ∏ i, sectorMass (v i)

end YangMills.Matching
