import YangMills.WilsonProof.TreeProfiles

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills YangMills.Hierarchy Function Filter MeasureTheory OPE OPE.Orbits OPE.Nesting Spec Table
open scoped Classical BigOperators Topology
variable {g : GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
local notation "H" => YangMills.hierarchy F Q

theorem spectatorsOnReader (uniform : Uniform F Q) (t : FusionTree) (a : Fin t.leaves → (H).Tag) {J : Type} [Fintype J]
      (b : J → (H).Tag) (h : ℕ) (M η ε δ : ℝ) (hM : 0 ≤ M) (hη : 0 < η)
      (hε : 0 < ε) (hδ : 0 < δ) (X : Type) [MeasurableSpace X] :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (s : t.Vertex → ℝ) (μ : Measure X) (q : X → ℂ),
      Integrable q μ → ∀ (x : X → Fin t.leaves → Spacetime) (z : X → t.Vertex → Spacetime)
      (y : X → J → Spacetime), AEMeasurable x μ → AEMeasurable z μ → AEMeasurable y μ →
      (∀ᵐ i ∂μ, q i ≠ 0 → t.separatedAt r M η s (x i) (z i) ∧ t.clearOf (x i) (z i) (y i) δ) →
      ∀ phase : Option (X → (H).Character), (∀ χ ∈ phase, AEMeasurable χ μ) →
        TestedDifference μ q (fun i => (H).grouped (phase.map (· i)) a (x i) b (y i))
          (fun i => (H).truncatedWithSpectators h (phase.map (· i)) a (x i) (z i 0) b (y i))
          (t.powerBound (H) ((h : ℝ) + 1) ε a s) := by
  let tags := a ∘ filedLeaves t
  have tested := uniform.tested (arity t 0) (childForest t) J tags b h M η ε δ hM hη hε hδ
  have joint := uniform.jointLaw (arity t 0) (childForest t) J tags b h M η ε δ hM hη hε hδ X
  filter_upwards [tested, joint] with r guard income
  intro s μ q integrable x z y mx mz my support phase measured
  let price := t.powerBound (H) ((h : ℝ) + 1) ε a s
  let first i := (H).grouped (phase.map (· i)) a (x i) b (y i)
  let second i := (H).truncatedWithSpectators h (phase.map (· i)) a (x i) (z i 0) b (y i)
  by_cases zero : q =ᵐ[μ] fun _ => 0
  · simpa only [mul_one] using (YangMills.WilsonProof.zeroTest zero first second price 1).2
  let plot i := filedPlot t (x i) (z i)
  let scales := s ∘ (filedLayout t).vertex
  have geometry : ∀ᵐ i ∂μ, q i ≠ 0 → Accept r M η scales (plot i) ∧ Buffer (plot i) (y i) δ :=
    support.mono fun i good nonzero =>
      ⟨atFiledTree t (good nonzero).1, atFiledExterior t (x i) (z i) (y i) δ (good nonzero).2⟩
  obtain ⟨k, hk, sample⟩ := YangMills.WilsonProof.onNonzeroTest zero geometry
  let mass := ∫ i, ‖q i‖ ∂μ
  have both := income scales μ mass q sample.1.1 integrable le_rfl plot y (filedMeasurable t mx mz) my geometry
  let panel := TestedProfile (filedTree t) plot y
  let viewer i : Viewers F := phase.map (· i)
  have result : JointEstimate F Q h (voices tags) (voices b)
      (mass * Nesting.Tree.toll (wages tags) ε (h+1 : ℝ) scales) μ q panel viewer := by
    cases phase with
    | none => exact both.2
    | some χ => exact both.1 χ (measured χ (by simp))
  let raw i := q i * whole (spectator F (viewer i)) (Nesting.Tree.profile (plot i)) (voices tags) (y i) (voices b)
  let cut i := q i * uponDiscount F Q h (voices tags) (voices b) (panel i) (viewer i)
  have rawEq : raw =ᵐ[μ] fun i => q i * first i := by
    filter_upwards [geometry] with i gi
    by_cases hi : q i = 0
    · simp [raw, hi]
    obtain ⟨accept, clear⟩ := gi hi
    have distinct := (guard scales (plot i) (y i) accept clear).1.2.1
    change Injective (beside (Nesting.Tree.profile (filedPlot t (x i) (z i))) (y i)) at distinct
    rw [filedPositions] at distinct
    exact congrArg (q i * ·) (filedWhole F Q t (viewer i) a (x i) (z i) b (y i)
      (original_injective (filedLeaves t) distinct))
  have cutEq : cut =ᵐ[μ] fun i => q i * second i :=
    .of_forall fun i => congrArg (q i * ·) (filedTruncation F Q t (viewer i) a (x i) (z i) b (y i) h)
  obtain ⟨rawIntegrable, cutIntegrable, _, recombine, bound⟩ := result
  refine ⟨rawIntegrable.congr rawEq, cutIntegrable.congr cutEq, ?_⟩
  rw [← integral_congr_ae rawEq, ← integral_congr_ae cutEq]
  change ‖(∫ i, raw i ∂μ) - ∫ i, cut i ∂μ‖ ≤ mass * price
  exact (congrArg norm recombine).trans_le (bound.trans_eq (congrArg (mass * ·) (filedToll t (H) a ((h : ℝ) + 1) ε s)))
end YM.Integration.WilsonSharpPhysicalTreeGeometry
