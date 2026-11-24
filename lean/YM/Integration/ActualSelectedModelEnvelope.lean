import YM.Integration.FullQLocalRetainedOutput
import YM.Integration.ActualNormalizedForcedMajorant

/-! The complete selected model and its raw residual under the original
finite-cutoff law. Envelopes below justify integration only; the remaining
flagged mass is kept explicitly and is not asserted to be small. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualSelectedModelEnvelope
open Function MeasureTheory Lattice Wilson RG Marker
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Script.Picnic
open scoped Classical BigOperators

section Envelope
variable {G : Gauge} {n : Side} {P : Rep G n} {p : BudgetPoint}

/-- Affine-nullness is unnecessary for the finite-volume envelope of the
complete regular sum. The requested and physical masks agree literally. -/
theorem additive_envelope (h : WellFormed p P) :
    Envelope (P.activities.additive P.p) := by
  obtain ⟨b, hb, hcost⟩ := Activities.E_total h.regular_bound
  have hd : Dominated (P.activities.regularOccurrence P.p) := by
    refine ⟨b, hb, ?_⟩
    intro i U
    unfold Activities.regularOccurrence
    rw [← h.threshold]
    by_cases hU : Healthy p.threshold (P.activities.reg i).support U
    · rw [masked_eq _ _ _ _ hU]
      exact (hcost i).2 U hU [] (Nat.zero_le _) (by simp)
    · rw [masked_ne _ _ _ _ hU, norm_zero]
      exact (hcost i).1
  refine ⟨?_, hd.bound⟩
  unfold Activities.additive
  apply Measurable.tsum
  intro i
  unfold Activities.regularOccurrence
  rw [← h.threshold]
  exact masked_measurable _ _ _ (h.regular i).borel

/-- The original path bound and the full regular budget suffice; no
vacuum positivity, affine reset or omitted soft gas is inserted here. -/
theorem exponent_envelope (h : WellFormed p P) {σ C Λ : ℝ}
    (hp : P.path.Bounds P.clip σ C Λ) : Envelope P.exponent := by
  have hc := PathData.channels_env (n := n) hp P.p P.beta
  have he := additive_envelope h
  unfold Rep.exponent
  simp_rw [sub_eq_add_neg]
  exact ((Envelope.const _).add hc.neg).add he.neg
end Envelope

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}

/-- Same chosen carrier, original path and clipping, and requested norm. -/
theorem chosen_exponent_envelope (hC : C.Makes) (S : Chosen K I M) :
    Envelope S.output.carrier.rep.exponent := by
  have hp := (hC.wilson.represents datum.cutoff datum.period datum.level
    datum.below.le).good.paths
  rw [← S.output.carrier.path, ← S.output.carrier.clip] at hp
  exact exponent_envelope S.wellFormed hp

/-- The entire raw flagged term, with its actual exponent and mask. -/
def flagNumerator (S : Chosen K I M) (forcedOrder : ℕ)
    (U : Config G (C.side datum.level datum.period)) : ℝ :=
  Real.exp (S.output.carrier.rep.exponent U) *
    ForcedNormalization.flagPrice S.output.carrier.rep.p.threshold
      (SectorNext.Vacuum.flagRate (A.outputNorm datum.level))
      ((Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
          (datum.level + 1)) ^ forcedOrder)) U

/-- Normalization is the original cutoff partition, not an auxiliary
vacuum or a lower bound selected after the tests. -/
def flagMass (S : Chosen K I M) (forcedOrder : ℕ) : ℝ :=
  (partition G (C.side datum.cutoff datum.period)
    (C.path.β datum.cutoff datum.period datum.cutoff))⁻¹ *
      ∫ U, flagNumerator S forcedOrder U ∂prior G (C.side datum.level datum.period)

theorem flagNumerator_integrable (hC : C.Makes) (S : Chosen K I M)
    (forcedOrder : ℕ) :
    Integrable (flagNumerator S forcedOrder)
      (prior G (C.side datum.level datum.period)) := by
  exact (((chosen_exponent_envelope hC S).exp).mul
    (ForcedNormalization.flagPrice_envelope _ _ _)).integrable _

end YM.Integration.ActualSelectedModelEnvelope
end
