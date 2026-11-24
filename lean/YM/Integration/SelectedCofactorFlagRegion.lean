import YM.Integration.SelectedCofactorFlagSelector

/-! The full physically normalized forcing on a field whose original flags
lie in the chosen region. No scalar or marked partner is removed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorFlagRegion
open Function Finset Set Filter MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate SelectedCofactorPacketIntegral
open SelectedCofactorConditionalSeries SelectedCofactorReplicatedFlags SelectedCofactorPhysicalMoment SelectedCofactorChamberMarginal
open scoped Classical BigOperators Topology
open SelectedCofactorPhysicalMoment SelectedCofactorChamberMarginal
variable {G : Gauge}
variable {V : Type} [DecidableEq V] [Fintype V] {B : Census V} {J : Request V}
variable {C : Family G} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F} {delta : ℝ} {order : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "W₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "Z₀" => partition G (C.side datum.cutoff datum.period) (C.path.β datum.cutoff datum.period datum.cutoff)

open ActualSelectedCoveredCofactor ActualSelectedModelIntegral

/-- A region captures the entire signed sum on every field where it contains
the distinguished address of every nonzero packet. -/
theorem of_roots (S : Chosen K I M) (x : IndependentTests J.tests) (X : Set (Site n₀))
    (Q : (ℕ × Finset ℕ) → Prop) (U : Config G n₀)
    (hX : ∀ a, packet S x a U ≠ 0 → (rootEdge S a.1).1 ∈ X) :
    rooted S x X Q U = ∑' a : ℕ × Finset ℕ, if Q a then packet S x a U else 0 := by
  let A₀ : Set (ℕ × Finset ℕ) := {a | (rootEdge S a.1).1 ∈ X ∧ Q a}
  let f (a : ℕ × Finset ℕ) := packet S x a U
  change (∑' a : A₀, f a.val) = ∑' a, if Q a then f a else 0
  rw [tsum_subtype A₀ f]
  apply tsum_congr
  intro a
  by_cases hn : f a = 0
  · simp only [Set.indicator,hn,ite_self]
  · simp only [Set.indicator,A₀,Set.mem_setOf_eq,hX a hn,true_and]

theorem entire (S : Chosen K I M) (x : IndependentTests J.tests) (X : Set (Site n₀))
    (Q : (ℕ × Finset ℕ) → Prop) (U : Config G n₀)
    (hX : ∀ z ∈ flags S.output.carrier.rep.p.threshold U, z ∈ X) :
    rooted S x X Q U = ∑' a : ℕ × Finset ℕ, if Q a then packet S x a U else 0 :=
  of_roots S x X Q U (fun a ha => hX _ (packet_inventory S x a U ha
    (S.output.carrier.rep.activities.forced a.1).inventory_ne.choose_spec))

/-- The exact full model defect less its original regular partner on the
whole physical flag event. A single dirty site in the region is included. -/
theorem normalized (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval = (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta order) (x : IndependentTests J.tests) (X : Set (Site n₀)) (U : Config G n₀)
    (hX : ∀ z ∈ flags S.output.carrier.rep.p.threshold U, z ∈ X) :
    ((C.path.rep datum.cutoff datum.period datum.level).eval U)⁻¹ • rooted S x X (fun _ => True) U =
      defect S (testInclusion J.tests x) U - S.output.modelValue (testInclusion J.tests x) U *
        (Poly.pass ((S.output.residual.leaf (testInclusion J.tests x)).log U) - 1) := by
  let z := (C.path.rep datum.cutoff datum.period datum.level).eval U
  let y := testInclusion J.tests x
  let b := S.output.modelValue y U * (Poly.pass ((S.output.residual.leaf y).log U) - 1)
  have hz : 0 < z := Multi.AxisShift.chosen_positive hC.wilson datum.below.le U
  have hw : z • defect S y U = z • b + forcedNumerator S y U :=
    ActualSelectedCofactorFunding.weighted_identity hG hC S hLate hFine H x U
  have ht := entire S x X (fun _ => True) U hX
  simp only [if_true] at ht
  rw [ht,forced_tsum hG hC S hLate H x U]
  change z⁻¹ • forcedNumerator S y U = defect S y U - b
  have he : forcedNumerator S y U = z • (defect S y U - b) := by
    rw [smul_sub,hw]
    abel
  rw [he,smul_smul,inv_mul_cancel₀ hz.ne',one_smul]

end YM.Integration.SelectedCofactorFlagRegion
end
