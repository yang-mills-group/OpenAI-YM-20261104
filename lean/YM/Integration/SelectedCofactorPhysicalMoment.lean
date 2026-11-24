import YM.Integration.SelectedCofactorHaarExchange
import YM.Integration.SelectedCofactorInsertionPrice
import YM.Integration.SelectedCofactorVacuumMass

/-! Signed conditional groups and their actual reflected copies under the
original finite Wilson partition. The exponent records the funding per chamber. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorPhysicalMoment

open Function Finset Filter MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate
open SelectedCofactorPacketIntegral SelectedCofactorConditionalSeries
open SelectedCofactorReplicatedFlags SelectedCofactorCommonVacuum SelectedCofactorJointBudget
open SelectedCofactorInsertionPrice
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

local notation "w₀" => (fun v => F.outputRadii v / F.kernelCosts v)
local notation "c₀" => MarkedPackets.uniformModelCost caps.packetRank (Fintype.card V) (K.geometry datum.level)
local notation "r₀" => Real.exp (Fintype.card V * ordinaryRate K I delta)
local notation "ε₀" => ((Fintype.card V : ℝ) * (forcedDivisor C datum.level *
    Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1) ^ forcedOrder))

local notation "Z₀" => partition G (C.side datum.cutoff datum.period) (C.path.β datum.cutoff datum.period datum.cutoff)
local notation "P₀" => C.path.rep datum.cutoff datum.period datum.level

/-- Explicit extensive path and calm-Haar costs minus the original dirty-field penalty. -/
def exposure (S : Chosen K I M) (regular s t : ℝ) (q : ℕ) : ℝ :=
  let P := S.output.carrier.rep
  let A₀ := (C.path.levels.params datum.level).paths
  let Λ := C.path.levels.clock.loopCap datum.level
  Fintype.card (Site n₀)*(2*P.exCost A₀ Λ regular + P.beta*RG.baseBudget P.clip A₀ s) +
    Fintype.card (Edge (Site n₀))*Module.finrank ℝ G.Mat*Real.log (16/s) - P.beta*(P.clip.linear/5*t^2*q)

theorem physical_price {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (hC : C.Makes) (S : Chosen K I M)
    (hFine : I.carrier.rep.eval = (C.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (hβ : 0 ≤ M.plan.predict datum.level) (regular : ℝ) (hR : S.output.carrier.rep.activities.EBound (A.outputNorm datum.level) regular)
    (s t : ℝ)
    (hs : 0 < s) (hS : s ≤ S.output.carrier.rep.p.threshold) (ht : 0 < t) (hT : 2*t ≤ S.output.carrier.rep.p.threshold)
    (f : Config G n₀ → E) (hf : Measurable f) (b : ℝ) (hb : ∀ U, ‖f U‖ ≤ b)
    (q : ℕ) (hq : ∀ U, f U ≠ 0 → q ≤ (flags t U).card) :
    Integrable (fun U => Real.exp (S.output.carrier.rep.exponent U) • f U) μ₀ ∧
    ‖Z₀⁻¹ • ∫ U, Real.exp (S.output.carrier.rep.exponent U) • f U ∂μ₀‖ ≤ b * Real.exp (exposure S regular s t q) := by
  have hGood := (hC.wilson.represents datum.cutoff datum.period datum.level datum.below.le).good
  have hpath := hGood.paths
  rw [← S.output.carrier.path, ← S.output.carrier.clip] at hpath
  have hEq := S.output.output_vacuum hC datum.below hFine
  have hb' : 0 ≤ S.output.carrier.rep.beta := by rw [S.vacuum.representation]; exact hβ
  have hI : Integrable S.output.carrier.rep.eval μ₀ := by rw [hEq]; exact ((P₀).envelope hGood).integrable _
  have hpos : ∀ U, 0 ≤ S.output.carrier.rep.eval U := by rw [hEq]; exact C.path.nonnegative hC.wilson _ _ _ datum.below.le
  have hZ : (∫ U, S.output.carrier.rep.eval U ∂μ₀) = Z₀ := by
    rw [hEq]; exact C.path.partition_eq hC.wilson _ _ _ datum.below.le
  have hr : 0 ≤ regular := by
    obtain ⟨_,_,he⟩ := hR
    simpa only [sum_empty] using Push.AbsoluteSums.budget_sum (he 0) ∅
  let W : WellFormed (A.outputNorm datum.level) S.output.carrier.rep :=
    { S.wellFormed with regularCost := regular, regular_cost_nonnegative := hr, regular_bound := hR }
  rw [←hZ]
  exact SelectedCofactorVacuumMass.signed_price W hpath hb' s t hs hS ht hT hpos hI f hf b hb q hq

/-- An original all-mode detector with its full relative marker price. -/
def detector (w : V → ℝ) (q : B.Mode) : Poly B →L[ℂ] ℂ := (Poly.toll w q : ℂ) • Poly.get q

omit [Fintype V] in
private theorem detector_price (w : V → ℝ) (hw : ∀v, 0 < w v) (q : B.Mode) (z : Poly B) :
    ‖detector w q z‖ ≤ Poly.price w z := by
  change ‖(Poly.toll w q : ℂ)*z.part q‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Poly.worth hw q).le]
  exact Poly.member hw q z

/-- Fixed geometry before the single-vacuum expectation. -/
def magnitude (K : NumericPrices A) (I : FullPreparedInputAt F eta_w) (caps : Handoff.OutputCapacities)
    (delta : ℝ) (forcedOrder d : ℕ) : ℝ :=
  (MarkedPackets.uniformModelCost caps.packetRank (Fintype.card V) (K.geometry datum.level) *
    Real.exp (Fintype.card V * ordinaryRate K I delta)) *
    (Real.exp (-((A.outputNorm datum.level).supportExponent * d)) *
      ((Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1) ^ forcedOrder)))

/-- The identities of every flag in an admitted packet, including every spectator. -/
def covered (S : Chosen K I M) (a : ℕ × Finset ℕ) : Finset (Site n₀) :=
  a.2.biUnion (fun i => (S.output.carrier.rep.activities.forced i).inventory)

theorem packet_covers (S : Chosen K I M) (x : IndependentTests J.tests) (a : ℕ × Finset ℕ)
    (U : Config G n₀) (hn : packet S x a U ≠ 0) :
    a.1 ∈ a.2 ∧ covered S a = flags S.output.carrier.rep.p.threshold U := by
  let D := S.output.residual.leaf (testInclusion J.tests x)
  have hf : cofactor D U a.1 a.2 ≠ 0 := fun hz => hn (by change rowKernel S x a.1 U * cofactor D U a.1 a.2 = 0; rw [hz,mul_zero])
  have hp := cofactor_support D U a.1 a.2 hf
  have ha := (CoveredSignedCofactors.pinned_erase_iff (fun i => (S.output.carrier.rep.activities.forced i).support)
    (fun i => (S.output.carrier.rep.activities.forced i).inventory) (fun i => (S.output.carrier.rep.activities.forced i).inventory_sup)
    (flags S.output.carrier.rep.p.threshold U) a.1 a.2).mp hp
  refine ⟨ha.2,?_⟩
  rw [←ha.1.2]
  ext z
  simp only [covered,mem_biUnion]

theorem covered_nonempty (S : Chosen K I M) (a : ℕ × Finset ℕ) (hi : a.1 ∈ a.2) : 1 ≤ (covered S a).card := by
  obtain ⟨z,hz⟩ := (S.output.carrier.rep.activities.forced a.1).inventory_ne
  exact card_pos.mpr ⟨z,mem_biUnion.mpr ⟨a.1,hi,hz⟩⟩

/-- The whole polynomial price of the signed preassigned conditional groups in
one original cutoff is paid before projecting or counting complete marker modes. -/
theorem grouped_price (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval = (C.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (hβ : 0 ≤ M.plan.predict datum.level) (regular : ℝ) (hR : S.output.carrier.rep.activities.EBound (A.outputNorm datum.level) regular)
    (H : Bounds S delta forcedOrder)
    (s t : ℝ) (hs : 0 < s) (hS : s ≤ S.output.carrier.rep.p.threshold) (ht : 0 < t) (hT : 2*t ≤ S.output.carrier.rep.p.threshold)
    (x : IndependentTests J.tests) (X : Set (Site n₀)) (Q : (ℕ × Finset ℕ) → Prop) (d m : ℕ)
    (hd : ∀ a, (rootEdge S a.1).1 ∈ X → Q a →
      d ≤ coverNumber (A.outputNorm datum.level).B (S.output.carrier.rep.activities.forced a.1).support)
    (hm : ∀ a, Q a → a.1 ∈ a.2 → m ≤ (covered S a).card) :
    Poly.price w₀ (Z₀⁻¹ • ∑' p : {a : ℕ × Finset ℕ // (rootEdge S a.1).1 ∈ X ∧ Q a}, exteriorPacket S x p.val) ≤
      magnitude K I caps delta forcedOrder d * Real.exp (exposure S regular s t m) := by
  let f := fun U => Poly.price w₀ (insertion S x X Q U)
  have hw v : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  have hb U : ‖f U‖ ≤ magnitude K I caps delta forcedOrder d := by
    change |Poly.price w₀ _| ≤ _
    rw [abs_of_nonneg (Poly.nonnegative hw _)]
    exact insertion_price hG hC S hLate H x X Q d hd U
  have hM : Measurable f := (Poly.price_cont w₀).measurable.comp (insertion_envelope hC S H x X Q).meas
  have hFlags U (hu : f U ≠ 0) : m ≤ (flags t U).card := by
    by_contra hn
    have hz (a : {a : ℕ × Finset ℕ // (rootEdge S a.1).1 ∈ X ∧ Q a}) : packet S x a.val U = 0 := by
      by_contra hp
      obtain ⟨hi,hc⟩ := packet_covers S x a.val U hp
      apply hn ((hm a.val a.property.2 hi).trans (card_le_card ?_))
      rw [hc]
      intro z he
      obtain ⟨u,hu,hit⟩ := (flags_spec _ _ _).1 he
      exact (flags_spec _ _ _).2 ⟨u,hu,(show t ≤ S.output.carrier.rep.p.threshold by linarith only [ht,hT]).trans_lt hit⟩
    have hzero : rooted S x X Q U = 0 := by rw [rooted,tsum_congr hz,tsum_zero]
    exact hu (by change Poly.price w₀ (Real.exp _ • rooted S x X Q U) = 0; rw [hzero,smul_zero,Poly.zero_price])
  have hp := (physical_price hC S hFine hβ regular hR s t hs hS ht hT f hM _ hb m hFlags).2
  have hZ : 0 ≤ Z₀⁻¹ := inv_nonneg.mpr (partition_pos _).le
  have hi : Integrable (rooted S x X Q) μ₀ := by
    have en := rooted_envelope hC S H x X Q
    obtain ⟨c,hc⟩ := en.cost
    exact Integrable.of_bound en.meas.aestronglyMeasurable c (ae_of_all _ hc)
  rw [←rooted_integral hC S H x X Q,ActualPolynomialContraction.price_real_smul w₀ _ hZ]
  calc
    _ ≤ Z₀⁻¹ * ∫ U, Poly.price w₀ (rooted S x X Q U) ∂μ₀ := mul_le_mul_of_nonneg_left
      (ActualPolynomialContraction.price_integral_le (F := rooted S x X Q) hw hi) hZ
    _ = Z₀⁻¹ • ∫ U, Real.exp (S.output.carrier.rep.exponent U) • f U ∂μ₀ := by
      congr 1
      apply integral_congr_ae (ae_of_all _ fun U => ?_)
      rw [←insertion_restore S x X Q U,ActualPolynomialContraction.price_real_smul w₀ _ (Real.exp_pos _).le]
      rfl
    _ ≤ _ := (le_abs_self _).trans hp

/-- The finite Wilson scene price with the prescribed ancestor or reflection
bins. Each bin sums every original coefficient in that group before pricing. -/
theorem scene_price {Iota : Type*} [Fintype Iota] (g : (ℕ × Finset ℕ) → Iota)
    (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval = (C.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (hβ : 0 ≤ M.plan.predict datum.level) (regular : ℝ) (hR : S.output.carrier.rep.activities.EBound (A.outputNorm datum.level) regular)
    (H : Bounds S delta forcedOrder)
    (s t : ℝ) (hs : 0 < s) (hS : s ≤ S.output.carrier.rep.p.threshold) (ht : 0 < t) (hT : 2*t ≤ S.output.carrier.rep.p.threshold)
    (x : IndependentTests J.tests) (d m : Iota → ℕ)
    (hd : ∀ i a, g a = i → d i ≤ coverNumber (A.outputNorm datum.level).B (S.output.carrier.rep.activities.forced a.1).support)
    (hm : ∀ i a, g a = i → a.1 ∈ a.2 → m i ≤ (covered S a).card) :
    Poly.price w₀ (∫ U, ActualSelectedModelIntegral.defect S (testInclusion J.tests x) U ∂scene C.path datum.cutoff datum.period datum.level) ≤
      c₀ * (r₀ - 1) + ∑ i, magnitude K I caps delta forcedOrder (d i) * Real.exp (exposure S regular s t (m i)) := by
  apply (SelectedCofactorHaarExchange.grouped_scene_price g hG hC S hLate hFine H x).trans
  apply add_le_add le_rfl
  apply sum_le_sum
  intro i _
  have h := grouped_price hG hC S hLate hFine hβ regular hR H s t hs hS ht hT x Set.univ (fun a => g a = i) (d i) (m i)
    (fun a _ ha => hd i a ha) (hm i)
  let E : {a : ℕ × Finset ℕ // (rootEdge S a.1).1 ∈ (Set.univ : Set (Site n₀)) ∧ g a = i} ≃
      {a : ℕ × Finset ℕ // g a = i} := Equiv.subtypeEquivRight (fun _ => by simp)
  rw [← E.tsum_eq (fun a => exteriorPacket S x a.val)]
  exact h

/-- Measurability and the pointwise product of the individual signed bounds
for the literal reflected original chamber observables. -/
theorem replica_bounds (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (H : Bounds S delta forcedOrder) (T : Tiling n₀) (x : T.Cell → IndependentTests J.tests)
    (X : T.Cell → Set (Site n₀)) (Q : T.Cell → (ℕ × Finset ℕ) → Prop) (q : T.Cell → B.Mode) (d : T.Cell → ℕ)
    (hd : ∀ i a, (rootEdge S a.1).1 ∈ X i → Q i a →
      d i ≤ coverNumber (A.outputNorm datum.level).B (S.output.carrier.rep.activities.forced a.1).support) :
    let f := T.fullAt (fun i W => detector w₀ (q i) (insertion S (x i) (X i) (Q i) W))
    Measurable f ∧ ∀ U, ‖f U‖ ≤ ∏ i, magnitude K I caps delta forcedOrder (d i) := by
  let f := fun i W => detector w₀ (q i) (insertion S (x i) (X i) (Q i) W)
  let b := fun i => magnitude K I caps delta forcedOrder (d i)
  have hw v : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  have hb i U : ‖f i U‖ ≤ b i := (detector_price w₀ hw (q i) _).trans
    (insertion_price hG hC S hLate H (x i) (X i) (Q i) (d i) (hd i) U)
  have hm i : Measurable (f i) := (detector w₀ (q i)).continuous.measurable.comp
    (insertion_envelope hC S H (x i) (X i) (Q i)).meas
  have hM : Measurable (T.fullAt f) := by
    apply Finset.measurable_fun_prod
    intro i _
    have hh := (hm i).comp (continuous_pull (T.omega i) (T.translateBy i)).measurable
    change Measurable (fun U => if T.hand i then star (f i (pull (T.omega i) (T.translateBy i) U)) else f i (pull (T.omega i) (T.translateBy i) U))
    by_cases hi : T.hand i
    · simp only [if_pos hi]
      exact continuous_star.measurable.comp hh
    simp only [if_neg hi]
    exact hh
  have hB U : ‖T.fullAt f U‖ ≤ ∏ i, b i := by
    rw [Tiling.fullAt,norm_prod]
    apply prod_le_prod (fun i _ => norm_nonneg _)
    intro i _
    by_cases hi : T.hand i
    · simpa only [Tiling.copy,if_pos hi,norm_star] using hb i (pull (T.omega i) (T.translateBy i) U)
    simpa only [Tiling.copy,if_neg hi] using hb i (pull (T.omega i) (T.translateBy i) U)
  exact ⟨hM,hB⟩

/-- The actual finite replica moment, with the common original vacuum, arbitrary
ancestor selections and a potentially different physical coefficient in each chamber. -/
theorem replica_price (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval = (C.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (hβ : 0 ≤ M.plan.predict datum.level) (regular : ℝ) (hR : S.output.carrier.rep.activities.EBound (A.outputNorm datum.level) regular)
    (H : Bounds S delta forcedOrder)
    (s t : ℝ) (hs : 0 < s) (hS : s ≤ S.output.carrier.rep.p.threshold) (ht : 0 < t) (hT : 2*t ≤ S.output.carrier.rep.p.threshold)
    (T : Tiling n₀) (x : T.Cell → IndependentTests J.tests) (X : T.Cell → Set (Site n₀))
    (hX : ∀ i, X i ⊆ T.chamber 0) (Q : T.Cell → (ℕ × Finset ℕ) → Prop) (q : T.Cell → B.Mode) (d : T.Cell → ℕ)
    (hd : ∀ i a, (rootEdge S a.1).1 ∈ X i → Q i a →
      d i ≤ coverNumber (A.outputNorm datum.level).B (S.output.carrier.rep.activities.forced a.1).support) :
    let f := T.fullAt (fun i W => detector w₀ (q i) (insertion S (x i) (X i) (Q i) W))
    Integrable (fun U => Real.exp (S.output.carrier.rep.exponent U) • f U) μ₀ ∧
    ‖Z₀⁻¹ • ∫ U, Real.exp (S.output.carrier.rep.exponent U) • f U ∂μ₀‖ ≤
      (∏ i, magnitude K I caps delta forcedOrder (d i)) * Real.exp (exposure S regular s t (Fintype.card T.Cell)) := by
  let f := fun i W => detector w₀ (q i) (insertion S (x i) (X i) (Q i) W)
  obtain ⟨hM,hB⟩ := replica_bounds hG hC S hLate H T x X Q q d hd
  apply physical_price hC S hFine hβ regular hR s t hs hS ht hT (T.fullAt f) hM _ hB
  intro U hu
  apply common_vacuum_flags S T x X hX Q (fun i => detector w₀ (q i)) (by linarith only [ht,hT]) U
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') hu

end YM.Integration.SelectedCofactorPhysicalMoment
end
