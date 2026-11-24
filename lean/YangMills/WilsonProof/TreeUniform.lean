import YangMills.WilsonProof.TreeContraction
import YangMills.WilsonProof.TreeSpectators

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills YangMills.Hierarchy Function Filter MeasureTheory OPE OPE.Orbits OPE.Nesting Spec Table
open scoped Classical BigOperators Topology
variable {g : GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
local notation "H" => YangMills.hierarchy F Q

theorem coefficientsOnReader (uniform : Uniform F Q) (t : FusionTree) (a : Fin t.leaves → (H).Tag) (D : Fin t.branches → ℕ)
      (w : ℕ) (c : (H).Channel w) (M η ε : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε)
      (X : Type) [MeasurableSpace X] :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (s : t.Vertex → ℝ) (μ : Measure X) (q : X → ℂ),
      Integrable q μ → ∀ (x : X → Fin t.leaves → Spacetime) (z : X → t.Vertex → Spacetime),
      AEMeasurable x μ → AEMeasurable z μ →
      (∀ᵐ i ∂μ, q i ≠ 0 → t.separatedAt r M η s (x i) (z i)) →
      let flat := fun i => (H).coefficient a w c (x i) (z i 0)
      let nested := fun i => t.iterated (H) a (x i) (z i) D w c
      let bound := t.powerBound (H) w ε a s
      ‖∫ i, q i * flat i ∂μ‖ ≤ (∫ i, ‖q i‖ ∂μ) * bound ∧
        TestedDifference μ q flat nested (bound * t.cutoffGain D s) := by
  let tags := a ∘ filedLeaves t
  have joint := uniform.joint (arity t 0) (childForest t) tags w c (filedCutoff t D) M η ε hM hη hε X
  filter_upwards [joint] with r income
  intro s μ q integrable x z mx mz support
  let first i := (H).coefficient a w c (x i) (z i 0)
  let second i := t.iterated (H) a (x i) (z i) D w c
  let price := t.powerBound (H) w ε a s
  by_cases zero : q =ᵐ[μ] fun _ => 0
  · exact YangMills.WilsonProof.zeroTest zero first second price (t.cutoffGain D s)
  let plot i := filedPlot t (x i) (z i)
  let scales := s ∘ (filedLayout t).vertex
  have geometry : ∀ᵐ i ∂μ, q i ≠ 0 → Accept r M η scales (plot i) :=
    support.mono fun i h nonzero => atFiledTree t (h nonzero)
  obtain ⟨i, hi, sample⟩ := YangMills.WilsonProof.onNonzeroTest zero geometry
  let mass := ∫ i, ‖q i‖ ∂μ
  obtain ⟨base, compounded, ask, dual⟩ := income scales sample.1 μ mass q plot integrable le_rfl
    (filedMeasurable t mx mz) geometry
  have flat : (fun i => q i * Kernel.output F Q (plot i) tags c) = (fun i => q i * first i) :=
    funext fun i => congrArg (q i * ·) (filedOutput F Q t a (x i) (z i) w c)
  have nested : (fun i => q i * Kernel.chord F Q (plot i) tags c (filedCutoff t D)) = (fun i => q i * second i) :=
    funext fun i => congrArg (q i * ·) (Contraction.filedChord F Q t a (x i) (z i) D w c)
  rw [flat] at base ask dual
  rw [nested] at compounded dual
  have priceEq := filedToll t (H) a w ε s
  have gainEq := filedGain t D s
  exact ⟨ask.trans_eq (congrArg (mass * ·) priceEq), ⟨base, compounded,
    dual.trans_eq (congrArg (mass * ·) (congrArg₂ (· * ·) priceEq gainEq))⟩⟩

theorem onFiledUniform (uniform : Uniform F Q) : PowerTreeExpansion (H) :=
  ⟨coefficientsOnReader F Q uniform, spectatorsOnReader F Q uniform⟩

end YM.Integration.WilsonSharpPhysicalTreeGeometry
