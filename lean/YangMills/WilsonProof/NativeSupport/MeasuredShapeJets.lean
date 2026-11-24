import YangMills.WilsonProof.NativeSupport.SeparatedCorrelationBounds

/-! Real relative shape derivatives of the two comparisons on the appointed measurement. -/
set_option autoImplicit false
noncomputable section

namespace YangMills.Matching

open Filter Set
open scoped BigOperators Topology Classical

/-- Both operands have genuine derivatives through the requested order at this configuration. -/
def shapeJetEstimateAt {n : ℕ} (j : ℕ) (actual predicted : Points n → ℂ)
    (x : Points n) (bound : ℝ) : Prop :=
  ContDiffAt ℝ j actual x ∧ ContDiffAt ℝ j predicted x ∧
    ∀ l ≤ j, ‖iteratedFDeriv ℝ l (fun y => actual y - predicted y) x‖ ≤ bound

variable {g : GaugeGroup} {B : Maxwell.Reference g}
variable {C : WilsonFamily g} {T : Hierarchy C}

/-- At fixed length only the relative insertion coordinates vary. The center, phase, fields
and output covector may all be chosen after the common length tail. -/
structure ShapeJetComparison (M : MSbar.Coefficients B) (S : Conversion B)
    (H : Measurement B T) : Prop where
  correlation (n p j : ℕ) (d : Fin n → ℕ) (K : Set (Points n))
      (compact : IsCompact K) (separated : K ⊆ WilsonFamily.separated n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ (phase : Option T.Character)
      (v : (i : Fin n) → B.sector (d i)) (o : Spacetime) (x : Points n), x ∈ K →
      let a : Fin n → Label B := fun i => ⟨d i, v i⟩
      shapeJetEstimateAt j
        (fun y => T.correlation phase (H.inputs s a) (WithLp.toLp 2 fun i => o + s • y i))
        (fun y => ∑ k : Fin (p+1), (H.clock s : ℂ)^k.val * S.correlation M k.val a y)
        x (A * (∏ i, sectorMass (v i)) * |H.clock s|^(p+1))
  ope (n h p j : ℕ) (d : Fin n → ℕ) (K : Set (Points n))
      (compact : IsCompact K) (separated : K ⊆ WilsonFamily.separated n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ∀ (v : (i : Fin n) → B.sector (d i)) (o : Spacetime) (x : Points n), x ∈ K →
      ∀ out : B.sector h →ₗ[ℂ] ℂ, (∀ w, ‖out w‖ ≤ sectorMass w) →
      let a : Fin n → Label B := fun i => ⟨d i, v i⟩
      shapeJetEstimateAt j
        (fun y => out (H.wilsonOPE s h a o y))
        (fun y => out (∑ k : Fin (p+1), (H.clock s : ℂ)^k.val • S.ope M h k.val a y))
        x (A * (∏ i, sectorMass (v i)) * |H.clock s|^(p+1))

end YangMills.Matching

