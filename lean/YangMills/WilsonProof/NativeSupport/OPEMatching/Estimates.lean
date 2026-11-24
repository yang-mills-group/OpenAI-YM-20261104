import YangMills.WilsonProof.NativeSupport.OPEMatching.PhysicalCoefficients
import YangMills.WilsonProof.NativeSupport.OPEMatching.Reference
import YangMills.WilsonProof.NativeSupport.MeasuredShapeJets

/-! The perturbative order and the engineering dimension of the output are
independent truncations. The position-scheme conversion acts on every input
and, inversely, on the output before comparison with the physical coefficient. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.OPEMatching

open Filter Matching
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}

/-- Order-`p` prediction in the same finite field space as the measured output. -/
def prediction (M : MSbar.Coefficients (maxwellReference g))
    (S : Conversion (maxwellReference g)) {n : ℕ} (h p : ℕ) (coupling : ℝ)
    (fields : Fin n → Label (maxwellReference g)) (x : Points n) : (maxwellReference g).sector h :=
  ∑ k : Fin (p + 1), (coupling : ℂ)^k.val • S.ope M h k.val fields x

/-- At every finite output horizon, the whole field has the prescribed series.
The smeared estimate tests every linear functional. The compact bound controls
the field itself, and the derivative bound is uniform on the dual unit ball. -/
structure Estimates (M : MSbar.Coefficients (maxwellReference g))
    (S : Conversion (maxwellReference g)) (H : CorrelationMatching.Measurement (maxwellReference g) T) :
    Prop where
  tested (n h : ℕ) (d : Fin n → ℕ) : ∃ m : ℕ,
    ∀ (v : (i : Fin n) → (maxwellReference g).sector (d i)) (center : Spacetime)
      (out : (maxwellReference g).sector h →ₗ[ℂ] ℂ),
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      HasExpansion m H.coupling (fun r x => out (physicalOutput H r h fields center x))
        (fun k x => out (S.ope M h k fields x))
  compact (n h p : ℕ) (d : Fin n → ℕ) (center : Spacetime) (K : Set (Points n)) :
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ (v : (i : Fin n) → (maxwellReference g).sector (d i)) (x : Points n), x ∈ K →
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      sectorMass (physicalOutput H r h fields center x - prediction M S h p (H.coupling r) fields x) ≤
        A * (∏ i, sectorMass (v i)) * |H.coupling r|^(p + 1)
  derivatives (n h p j : ℕ) (d : Fin n → ℕ) (K : Set (Points n)) :
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ (v : (i : Fin n) → (maxwellReference g).sector (d i)) (center : Spacetime)
        (x : Points n), x ∈ K → ∀ out : (maxwellReference g).sector h →ₗ[ℂ] ℂ,
      (∀ w, ‖out w‖ ≤ sectorMass w) →
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      shapeJetEstimateAt j (fun y => out (physicalOutput H r h fields center y))
        (fun y => out (prediction M S h p (H.coupling r) fields y)) x
        (A * (∏ i, sectorMass (v i)) * |H.coupling r|^(p + 1))

end YangMills.OPEMatching
