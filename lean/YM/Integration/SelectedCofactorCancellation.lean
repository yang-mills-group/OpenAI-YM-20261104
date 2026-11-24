import YM.Integration.ActualSelectedCofactorFunding
import YM.Integration.ActualSelectedCofactorHaar

/-! Signed cofactor coefficients on the original carrier and cover. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.SelectedCofactorCancellation

open Function Finset Filter MeasureTheory Lattice Wilson RG Marker Overlay
open RG3.Forms RG3.Script.Picnic OPE.Therm LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate
open ActualSelectedCoveredCofactor ActualSelectedModelIntegral ActualSelectedModelEnvelope
open scoped Classical BigOperators

section Rows

variable {G : Gauge} {n : Side} {P : Rep G n}
  {V : Type} [DecidableEq V] {B : Census V}

/-- The remaining *original* vacuum rows on the admitted packet. -/
def pinnedVacuum (P : Rep G n) (U : Config G n) (i : ℕ) (s : Finset ℕ) : ℂ :=
  if admitted P U i s then ∏ j ∈ s.erase i, (P.activities.K j U : ℂ) else 0

variable (D : Deck B P)
  (hot : ∀ i j, (D.contents.marks i j).val.Nonempty)

include hot in
private theorem each_quiet (U : Config G n) (i : ℕ) :
    (D.contents.each i U).part B.quiet = (P.activities.K i U : ℂ) := by
  rw [Bands.each, Poly.part_plus, Poly.part_send, if_pos rfl]
  by_cases hs : Summable (fun j => D.contents.tagged i j U)
  · rw [Poly.share hs]
    have hz (j : ℕ) : (D.contents.tagged i j U).part B.quiet = 0 := by
      rw [Bands.tagged, Poly.part_send, if_neg]
      intro he
      exact (hot i j).ne_empty (congrArg Subtype.val he.symm)
    simp only [hz, tsum_zero, add_zero]
  rw [tsum_eq_zero_of_not_summable hs, Poly.part_nil, add_zero]

private theorem scalar_quiet (U : Config G n) (i : ℕ) :
    (scalarRow P U i : Poly B).part B.quiet = (P.activities.K i U : ℂ) := by
  change (Poly.send B.quiet _).part B.quiet = _
  exact (Poly.part_send ..).trans (if_pos rfl)

private theorem scalar_nonquiet (U : Config G n) (i : ℕ) (s : B.Mode)
    (hs : s ≠ B.quiet) : (scalarRow P U i : Poly B).part s = 0 := by
  change (Poly.send B.quiet _).part s = _
  exact (Poly.part_send ..).trans (if_neg hs)

include hot in
private theorem row_quiet (U : Config G n) (i : ℕ) :
    (D.contents.each i U - scalarRow P U i).part B.quiet = 0 := by
  rw [Extra.Trajectories.part_sub, each_quiet D hot, scalar_quiet, sub_self]

include hot in
theorem cofactor_quiet (U : Config G n) (i : ℕ) (s : Finset ℕ) :
    (cofactor D U i s).part B.quiet = pinnedVacuum P U i s := by
  rw [cofactor_eq_if]
  unfold pinnedVacuum
  by_cases ha : admitted P U i s
  · rw [if_pos ha, if_pos ha]
    unfold remainingProduct CoveredSignedCofactors.mixed
    rw [MergeProof.Accent.shockProd₀ B]
    apply prod_congr rfl
    intro j _
    split
    · exact scalar_quiet U j
    · exact each_quiet D hot U j
  rw [if_neg ha, if_neg ha, Poly.part_nil]

include hot

/-- Every surviving partition gives the distinguished row a nonempty
subset of the requested marks. All disjoint partners on the remaining
marks are still present. -/
theorem row_times_part (U : Config G n) (i : ℕ) (L : Poly B) (s : B.Mode) :
    ((D.contents.each i U - scalarRow P U i) * L).part s =
      ∑ a : B.Mode, ∑ b : B.Mode, if a ≠ B.quiet ∧ Poly.merges a b s then
        (D.contents.each i U).part a * L.part b else 0 := by
  rw [Poly.part_mul]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases ha : a = B.quiet
  · subst a
    simp [row_quiet D hot U i]
  by_cases hm : Poly.merges a b s
  · rw [if_pos hm, if_pos ⟨ha, hm⟩, Extra.Trajectories.part_sub,
      scalar_nonquiet U i a ha, sub_zero]
  rw [if_neg hm, if_neg (fun h => hm h.2)]

/-- Once the distinguished row owns the singleton, its remaining packet
contributes precisely its original vacuum coefficient. -/
theorem row_times_singleton (U : Config G n) (i : ℕ) (s : Finset ℕ) (v : V) :
    ((D.contents.each i U - scalarRow P U i) * cofactor D U i s).part (B.fire v) =
      (D.contents.each i U).part (B.fire v) * pinnedVacuum P U i s := by
  rw [MergeProof.Accent.shock B]
  rw [row_quiet D hot, zero_mul, zero_add, cofactor_quiet D hot,
    Extra.Trajectories.part_sub, scalar_nonquiet U i _ (B.fire_hot v), sub_zero]

/-- The countable physical cofactor expansion has zero quiet component.
The subtraction cancels separately at every distinguished row. -/
theorem series_quiet (U : Config G n)
    (hs : Summable (fun i => (D.contents.each i U - scalarRow P U i) *
      ∑' s, cofactor D U i s)) : (series D U).part B.quiet = 0 := by
  rw [series, Poly.share hs]
  exact (tsum_congr (fun i => by rw [Poly.quiet_mul, row_quiet D hot, zero_mul])).trans tsum_zero

omit hot in
/-- The complete signed forced singleton on the original admitted packets. -/
def singletonRows (U : Config G n) (v : V) : ℂ :=
  ∑' i, (D.contents.each i U).part (B.fire v) * ∑' s, pinnedVacuum P U i s

theorem series_singleton (U : Config G n) (v : V)
    (hi : ∀ i, Summable (cofactor D U i))
    (hs : Summable (fun i => (D.contents.each i U - scalarRow P U i) *
      ∑' s, cofactor D U i s)) : (series D U).part (B.fire v) = singletonRows D U v := by
  rw [series, Poly.share hs]
  refine tsum_congr fun i => ?_
  rw [MergeProof.Accent.shock B, row_quiet D hot, zero_mul, zero_add,
    Extra.Trajectories.part_sub, scalar_nonquiet U i _ (B.fire_hot v), sub_zero,
    Poly.share (hi i)]
  exact congrArg (_ * ·) (tsum_congr (cofactor_quiet D hot U i))

end Rows

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {forcedOrder : ℕ}

local notation "P₀" => C.path.rep datum.cutoff datum.period datum.level

/-- At one mark, every nonlinear model partner and every marked minor
disappears before integration. All original signed rows, admissibility masks,
and scalar pinned products remain inside the physical numerator. -/
theorem numerator_singleton (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) (v : V) :
    (numerator S (testInclusion J.tests x) U).part (B.fire v) =
      (P₀).eval U • ((S.output.residual.leaf (testInclusion J.tests x)).log U).part (B.fire v) +
      Real.exp (S.output.carrier.rep.exponent U) •
        singletonRows (S.output.residual.leaf (testInclusion J.tests x)) U v := by
  let X := testInclusion J.tests x
  let D := S.output.residual.leaf X
  have hot (i j) : (D.contents.marks i j).val.Nonempty := (H.residual_price.budget.active x).articles.occurs i j
  have hs := covered_series S H
    ((eventually_atTop.1 (actual_forced_smallness C hG hC (Fintype.card V))).choose_spec
      datum.level hLate datum.cutoff datum.period datum.below forcedOrder) x U
  have hQ : (D.log U).part B.quiet = 0 := by
    change (((pullback (testInclusion J.tests) S.output.residual).leaf x).log U).part B.quiet = 0
    rw [log_constant_split, Poly.part_plus,
      H.residual_price.constantLog_quiet F.kernel_positive S.wellFormed.threshold,
      H.residual_price.nativeRayLog_quiet F.kernel_positive S.wellFormed.threshold, add_zero]
  have hM : (S.output.modelValue X U).part B.quiet = 1 :=
    Poly.pass_part _ (S.output.model.quiet_read X _ U)
  have hp := Poly.pass_part _ hQ
  have hs₀ := series_quiet D hot U hs.2.1
  have hs₁ := series_singleton D hot U v hs.1 hs.2.1
  change (P₀).eval U • (S.output.modelValue X U * (Poly.pass (D.log U) - 1)).part (B.fire v) +
    Real.exp (S.output.carrier.rep.exponent U) •
      (S.output.modelValue X U * (Poly.pass (D.log U) * series D U)).part (B.fire v) = _
  simp only [MergeProof.Accent.shock B, Poly.quiet_mul, Extra.Trajectories.part_sub,
    Poly.one_part, B.fire_hot v, if_false, if_true, hM, hp, hs₀, hs₁,
    MergeProof.Accent.whisper B _ hQ, sub_zero, sub_self, one_mul, mul_zero, add_zero]
  rfl

end YM.Integration.SelectedCofactorCancellation
end
