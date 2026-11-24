import YM.Integration.SelectedCofactorFlagSelector
import YM.Integration.SelectedCofactorPuncturedVacuum
import YM.Integration.QLocalForcedBarcodeWitness
import YM.Integration.ActualNextLocalDatum

/-! Original marked test addresses and actual field flags for the
distinguished row of every nonzero selected residual packet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorResidualGeometry
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open LocalComparison LocalComparison.Global RG3.Forms RG3.Script.Picnic
open IterationFour IterationFour.Vacuum Comparison.RG02 PhysicalNext.Repeat.Legato
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open MergeProof MergeProof.Accent Push.AbsoluteSums Push.GridApprox.Attach
open NativeTasteCoveredCofactor SelectedCofactorPuncturedVacuum
open SelectedCofactorPacketIntegral SelectedCofactorConditionalSeries SelectedCofactorReplicatedFlags
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {order : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "w₀" => fun v => F.outputRadii v / F.kernelCosts v

/-- A positive-mode coefficient in the actual raw residual row retains
all prescribed addresses and the exact compulsory dirty inventory. -/
theorem indexed (S : Chosen K I M) (H : Bounds S delta order) (x : IndependentTests J.tests)
    (i : ℕ) (U : Config G n₀) (q : B.Mode) (hne : q ≠ B.quiet)
    (hs : (changeRow (S.output.residual.leaf (testInclusion J.tests x)) U i).part q ≠ 0) :
    QLocalForcedBarcodeWitness.Rooted F.outputAddresses
      (barcode S.output.carrier.rep.activities i) q (flags S.output.carrier.rep.p.threshold U) := by
  let T := pullback (testInclusion J.tests) S.output.residual
  let c := envelopeProduct F.kernelCosts (R := B)
  let D := T.leaf x
  have hc : ∀ q, 0 < c q := envelopeProduct_positive F.kernel_positive
  have he : ((T.menu.terms x).each i U).part q ≠ 0 := by
    change (D.contents.each i U).part q ≠ 0
    change (D.contents.each i U).part q - (Poly.send B.quiet (S.output.carrier.rep.activities.K i U : ℂ)).part q ≠ 0 at hs
    simpa only [Poly.part_send,if_neg hne,sub_zero] using hs
  let bill : ForcedBudget (A.outputNorm datum.level) T w₀ (forcedDivisor C datum.level)
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level+1)^order) :=
    QLocalForcedTestInvoice.restore _ _ F.kernelCosts F.kernel_positive
      ⟨H.residual_price.budget.black,H.residual_price.budget.black_nonnegative,
       H.residual_price.budget.forced,H.residual_price.budget.forcedTotal⟩
  obtain ⟨j,hq,hrow⟩ := QLocalForcedBarcodeWitness.at_index _ T bill
    (fun v => div_pos (F.output_radius_positive v) (F.kernel_positive v))
    (fun a b => (H.residual_price.budget.active x).articles.occurs a b)
    i (x,U) q hne he
  have hz : (c (T.menu.marks i j))⁻¹ • T.menu.force x i j U ≠ 0 :=
    smul_ne_zero (inv_ne_zero (hc _).ne') hrow
  rw [← hq]
  exact ⟨fun v hv => S.residual_retains.forced i j v ⟨testInclusion J.tests x,U,hrow⟩ hv,
    (S.output.carrier.rep.activities.forced i).inventory_ne,
    (S.output.carrier.rep.activities.forced i).inventory_sup,
    ((H.residual_price.budget.active x).articles.keeps i j U hz).1⟩

/-- The actual quiet coefficient of a changed row vanishes. -/
theorem row_mode (S : Chosen K I M) (H : Bounds S delta order) (x : IndependentTests J.tests)
    (i : ℕ) (U : Config G n₀) (hc : changeRow (S.output.residual.leaf (testInclusion J.tests x)) U i ≠ 0) :
    ∃ q : B.Mode, q ≠ B.quiet ∧
      (changeRow (S.output.residual.leaf (testInclusion J.tests x)) U i).part q ≠ 0 := by
  let D := S.output.residual.leaf (testInclusion J.tests x)
  by_contra hn
  apply hc
  change (fun q => (changeRow D U i).part q) = (fun _ : B.Mode => (0 : ℂ))
  funext q
  by_cases hq : q = B.quiet
  · rw [hq]
    exact quiet H.residual_price F.kernel_positive x U i
  · by_contra hz
    exact hn ⟨q,hq,hz⟩

/-- Every nonzero complete packet features a true positive-mode
coefficient at its distinguished original row. -/
theorem packet_row (S : Chosen K I M) (H : Bounds S delta order) (x : IndependentTests J.tests)
    (a : ℕ × Finset ℕ) (U : Config G n₀) (h : packet S x a U ≠ 0) :
    ∃ q : B.Mode, q ≠ B.quiet ∧
      (changeRow (S.output.residual.leaf (testInclusion J.tests x)) U a.1).part q ≠ 0 := by
  let D := S.output.residual.leaf (testInclusion J.tests x)
  have hc : changeRow D U a.1 ≠ 0 := by
    intro he
    apply h
    change multiplier S x U * changeRow D U a.1 * cofactor D U a.1 a.2 = 0
    rw [he,mul_zero,zero_mul]
  exact row_mode S H x a.1 U hc

/-- The actual distinguished inventory site of each nonzero packet is
dirty and lies within the original cover radius of a prescribed test root. -/
theorem packet_anchor (S : Chosen K I M) (H : Bounds S delta order) (x : IndependentTests J.tests)
    (a : ℕ × Finset ℕ) (U : Config G n₀) (b : ℕ) (h : packet S x a U ≠ 0) :
    (rootEdge S a.1).1 ∈ flags S.output.carrier.rep.p.threshold U ∧ ∃ v : V,
      separation (F.coarseRoots v) (rootEdge S a.1).1 <
        (coverNumber b (S.output.carrier.rep.activities.forced a.1).support + 1) * leg b := by
  obtain ⟨q,hq,hrow⟩ := packet_row S H x a U h
  have hr := indexed S H x a.1 U q hq hrow
  have hne : q.val.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun e => hq (Subtype.ext e)
  obtain ⟨v,hv⟩ := hne
  have hi : (rootEdge S a.1).1 ∈ (S.output.carrier.rep.activities.forced a.1).inventory :=
    (S.output.carrier.rep.activities.forced a.1).inventory_ne.choose_spec
  have hd := hr.near b hi
  exact ⟨hd.1,v,hd.2 v hv _ (ActualNextLocalDatum.output_roots_mem F v)⟩

/-- Outside the physical neighborhood of every prescribed root the
complete signed selected group has only large distinguished supports. -/
theorem only_large (S : Chosen K I M) (H : Bounds S delta order) (x : IndependentTests J.tests)
    (X : Set (Site n₀)) (Q : (ℕ × Finset ℕ) → Prop) (U : Config G n₀) (b k : ℕ)
    (hclean : ∀ v : V, ∀ y ∈ flags S.output.carrier.rep.p.threshold U,
      (k+1)*leg b ≤ separation (F.coarseRoots v) y) :
    rooted S x X Q U = rooted S x X (fun a =>
      Q a ∧ k < coverNumber b (S.output.carrier.rep.activities.forced a.1).support) U := by
  let E : Set (ℕ × Finset ℕ) := {a | (rootEdge S a.1).1 ∈ X ∧ Q a}
  let E' : Set (ℕ × Finset ℕ) := {a | (rootEdge S a.1).1 ∈ X ∧
    (Q a ∧ k < coverNumber b (S.output.carrier.rep.activities.forced a.1).support)}
  let f (a : ℕ × Finset ℕ) := packet S x a U
  change (∑' a : E, f a.val) = ∑' a : E', f a.val
  rw [tsum_subtype E f,tsum_subtype E' f]
  apply tsum_congr
  intro a
  by_cases h : f a = 0
  · simp only [Set.indicator,h,ite_self]
  · obtain ⟨hy,v,hv⟩ := packet_anchor S H x a U b h
    have hb : k < coverNumber b (S.output.carrier.rep.activities.forced a.1).support := by
      by_contra! hk
      have he := Nat.mul_le_mul_right (leg b) (Nat.succ_le_succ hk)
      exact (not_lt_of_ge (hclean v _ hy)) (hv.trans_le he)
    simp only [Set.indicator,E,E',Set.mem_setOf_eq,hb,and_true]
    by_cases hp : (rootEdge S a.1).1 ∈ X ∧ Q a
    · simp only [if_pos hp]
    · simp only [if_neg hp]

end YM.Integration.SelectedCofactorResidualGeometry
end
