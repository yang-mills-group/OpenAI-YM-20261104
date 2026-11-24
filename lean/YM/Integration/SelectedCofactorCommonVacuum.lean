import YM.Integration.SelectedCofactorReplicatedFlags

/-! The physical exponential is applied once to a product of reflected signed insertions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorCommonVacuum

open Function Finset Filter MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate
open SelectedCofactorPacketIntegral SelectedCofactorConditionalSeries
open SelectedCofactorReplicatedFlags
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {forcedOrder : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "μ₀" => prior G n₀

/-- Remove the single original exponential from the complete signed packet group.
The model, pass factors, distinguished row and all original partners stay inside. -/
def insertion (S : Chosen K I M) (x : IndependentTests J.tests) (X : Set (Site n₀))
    (Q : (ℕ × Finset ℕ) → Prop) (U : Config G n₀) : Poly B :=
  Real.exp (-S.output.carrier.rep.exponent U) • rooted S x X Q U

/-- Restoring the original exponential recovers exactly the signed numerator group. -/
theorem insertion_restore (S : Chosen K I M) (x : IndependentTests J.tests) (X : Set (Site n₀))
    (Q : (ℕ × Finset ℕ) → Prop) (U : Config G n₀) :
    Real.exp (S.output.carrier.rep.exponent U) • insertion S x X Q U = rooted S x X Q U := by
  rw [insertion, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

theorem insertion_envelope (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (X : Set (Site n₀)) (Q : (ℕ × Finset ℕ) → Prop) :
    Envelope (insertion S x X Q) := by
  have he := (ActualSelectedModelEnvelope.chosen_exponent_envelope hC S).neg.exp
  have hf := rooted_envelope hC S H x X Q
  obtain ⟨a,ha⟩ := he.cost
  obtain ⟨b,hb⟩ := hf.cost
  refine ⟨he.meas.smul hf.meas, a*b, fun U => ?_⟩
  exact (norm_smul_le _ _).trans (mul_le_mul (ha U) (hb U) (norm_nonneg _) ((norm_nonneg _).trans (ha U)))

theorem signed_insertion_integral (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (X : Set (Site n₀)) (Q : (ℕ × Finset ℕ) → Prop) :
    (∫ U, Real.exp (S.output.carrier.rep.exponent U) • insertion S x X Q U ∂μ₀) =
      ∑' p : {p : ℕ × Finset ℕ // (rootEdge S p.1).1 ∈ X ∧ Q p}, exteriorPacket S x p.val := by
  simp_rw [insertion_restore]
  exact rooted_integral hC S H x X Q

/-- Arbitrary reflected detections of the individual insertions, with one
original vacuum outside the product. The root sites give distinct physical flags. -/
theorem common_vacuum_flags (S : Chosen K I M) (T : Tiling n₀) (x : T.Cell → IndependentTests J.tests)
    (X : T.Cell → Set (Site n₀)) (hX : ∀ i, X i ⊆ T.chamber 0)
    (Q : T.Cell → (ℕ × Finset ℕ) → Prop) (L : T.Cell → Poly B →L[ℂ] ℂ)
    {t : ℝ} (ht : t ≤ S.output.carrier.rep.p.threshold) (U : Config G n₀)
    (hn : (Real.exp (S.output.carrier.rep.exponent U) : ℂ) *
      T.fullAt (fun i W => L i (insertion S (x i) (X i) (Q i) W)) U ≠ 0) :
    Fintype.card T.Cell ≤ (flags t U).card := by
  apply replicated_flags S T x X hX Q L ht U
  unfold Tiling.fullAt
  apply prod_ne_zero_iff.mpr
  intro i _
  let W := pull (T.omega i) (T.translateBy i) U
  have hfree : L i (insertion S (x i) (X i) (Q i) W) ≠ 0 := by
    intro hz
    apply hn
    rw [mul_eq_zero]
    right
    apply prod_eq_zero (mem_univ i)
    unfold Tiling.copy
    split
    · change star (L i (insertion S (x i) (X i) (Q i) W)) = 0
      rw [hz, star_zero]
    · exact hz
  have hpaid : L i (rooted S (x i) (X i) (Q i) W) ≠ 0 := by
    intro hz
    apply hfree
    change (L i).restrictScalars ℝ (Real.exp (-S.output.carrier.rep.exponent W) • rooted S (x i) (X i) (Q i) W) = 0
    rw [map_smul, show (L i).restrictScalars ℝ (rooted S (x i) (X i) (Q i) W) = 0 from hz, smul_zero]
  unfold Tiling.copy
  split <;> simpa only [ne_eq, star_eq_zero] using hpaid

end YM.Integration.SelectedCofactorCommonVacuum
end
