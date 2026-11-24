import YM.Integration.ActualInputVertexPrice
import YM.Integration.PatternPhysicalTensorPrice

/-! The original real geometric derivative as a complex normalized tensor and
its literal full Option-table marginal. No factorial or sign is suppressed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualInputVertexTable
open Function Filter Lattice Wilson RG Precision Tree Exterior Marker
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Push.Uniform Comparison.RG02
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical ContDiff

/-- Only the real-to-complex scalar map is applied to the normalized tensor. -/
def complexCoeff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (n : ℕ) : Tensor.T E ℂ n :=
  Complex.ofRealCLM.compContinuousMultilinearMap (Tensor.coeff f n 0)

/-- The full original Array field coordinate map, with zero coupling. -/
def fieldFrame {G : Gauge} {c f : Side} {S : StepData c f} (B : Forest S.ratio) :
    Positions (Push.Uniform.Joint B G) →L[ℝ] Bulk.Joint S B (G := G) :=
  (0 : Positions (Push.Uniform.Joint B G) →L[ℝ] ℝ).prod
    (paint B G).toContinuousLinearMap

/-- The table keeps precisely the original factorial-normalized derivative. -/
theorem table_apply {G : Gauge} {c f : Side} {S : StepData c f}
    (B : Forest S.ratio) (h : Bulk.Joint S B (G := G) → ℝ)
    (n : ℕ) (z : Fin n → Option (Push.Uniform.Joint B G)) :
    PatternPhysicalTensorPrice.table (1, 0) (fieldFrame B) (complexCoeff h n) z =
      ((n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n h 0
        (fun k => ActualInputVertexPrice.frame B
          (FiniteOptionSlotMarginal.direction (fun i => bolt i) (z k))) : ℝ) := by
  have hv : (fun k => (z k).elim (1, 0)
      (fun i => fieldFrame B (Pi.single i 1))) =
      (fun k => ActualInputVertexPrice.frame B
        (FiniteOptionSlotMarginal.direction (fun i => bolt i) (z k))) := by
    funext k
    cases z k <;>
      simp [fieldFrame, ActualInputVertexPrice.frame,
        FiniteOptionSlotMarginal.direction, bolt]
  unfold PatternPhysicalTensorPrice.table
  rw [hv]
  rfl

private theorem sum_fixed {I : Type*} [Fintype I] [DecidableEq I]
    (k : ℕ) (j : Fin (k + 1)) (i0 : I) (F : (Fin (k + 1) → I) → ℝ) :
    (∑ z : Fin (k + 1) → I, if z j = i0 then F z else 0) =
      ∑ q : Fin k → I, F (Fin.insertNth j i0 q) := by
  rw [← (Fin.insertNthEquiv (fun _ : Fin (k + 1) => I) j).sum_comp
    (fun z => if z j = i0 then F z else 0)]
  change (∑ p : I × (Fin k → I),
    if Fin.insertNth (α := fun _ => I) j p.1 p.2 j = i0 then F (Fin.insertNth (α := fun _ => I) j p.1 p.2) else 0) = _
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp

/-- One fixed constant and one event precede all original data and tables. -/
theorem vertices {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (A : NumericSchedule T.family J) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, ∀ᶠ i : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = i →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (x : TestSpace J.tests)
        (B : Forest (T.family.path.levels.clock.op datum.level datum.period).ratio)
        (t : (T.family.path.levels.clock.op datum.level datum.period).Choices),
      ∀ k : ℕ, k + 1 ≤ J.order + 2 → ∀ j : Fin (k + 1),
        ∀ i0 : Push.Uniform.Joint B G,
        (∑ z : Fin (k + 1) → Option (Push.Uniform.Joint B G),
          if z j = some i0 then
            ‖PatternPhysicalTensorPrice.table (1, 0) (fieldFrame B)
              (complexCoeff (Bulk.geometric (datum.kernel Y) B t (I.colors x)) (k + 1)) z‖
          else 0) ≤ C * (A.admittedCost i) ^ e := by
  obtain ⟨C, hC, e, h⟩ := ActualInputVertexPrice.vertices T hG hT (R := R) A
  refine ⟨C, hC, e, ?_⟩
  filter_upwards [h] with i hi
  intro datum hlevel Y I x B t k hk j i0
  rw [sum_fixed]
  simpa only [table_apply, Complex.norm_real, Real.norm_eq_abs] using
    hi datum hlevel Y I x B t k hk j i0

end YM.Integration.ActualInputVertexTable
end
