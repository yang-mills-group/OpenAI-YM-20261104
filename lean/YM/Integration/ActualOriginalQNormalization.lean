import YM.Integration.FullQLocalFixedRadiusScaling
import YM.Integration.ActualOriginalQCharges

/-! The literal original-Q finite bill gives a pre-test normalization at
unchanged radii. Its inverse factor remains in every restored full defect.
The cutoff clock N is not identified with a later stage clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQNormalization
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open ActualOriginalQReaders ActualOriginalQPackets
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
    {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
    (Q : MS.Land.Prescription B)
    (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
    (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)

/-- This is the full original fee/reader/tensor/path bill after the proved
regulator and threshold cancellation. It may depend on N, p and L. -/
def normalizer (N : ℕ) (w : V → ℝ) (width : ℝ) : ℝ :=
  max 1 (∑ s : Row (R := R) u,
    ‖fee Q u (μ - R.family.S.scale N) orders s.1‖ *
      ActualOriginalQCharges.rowPrice D u w width s)

/-- The derived normalization pays all original packet rows at fixed radii.
It does not pay inverse normalization in a uniform later-stage error. -/
theorem normalized_paid (N : ℕ) (hL : L ≤ N) (P : BudgetPoint)
    (w : V → ℝ) (width : ℝ) (hwidth : 0 < width) (hw : ∀ i, 0 < w i) :
    (FullQLocal.VariableScaling.packets
      (fun _ : V => (normalizer Q D u μ orders N w width : ℂ)⁻¹)
      (packets Q D u (μ - R.family.S.scale N) orders N)).Paid
      P (positions D u).stub (ActualRunQlocalNativeTuple.readerRegion D) w
      (Pert.Asymptotics.regulatorRun R.family N p L) width 1
      (packetCover Q D u (μ - R.family.S.scale N) orders N P) 0 := by
  apply FullQLocal.FixedRadiusScaling.paid_normalized
    (packets Q D u (μ - R.family.S.scale N) orders N)
    (packets_paid Q D u (μ - R.family.S.scale N) orders N P w width hwidth hw)
    (normalizer Q D u μ orders N w width)
  · exact le_max_left _ _
  · rw [ActualOriginalQCharges.packet_cost D u Q
      (μ - R.family.S.scale N) orders N hL w width]
    exact le_max_right _ _

end YM.Integration.ActualOriginalQNormalization
end
