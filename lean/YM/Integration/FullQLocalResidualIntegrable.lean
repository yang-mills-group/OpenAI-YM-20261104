import YM.Integration.FullQLocalProducedOutput
import YM.Integration.LocalComparisonModelIntegrable
import YM.Integration.FullQLocalCaptionTransport

/-! Genuine L1 of the chosen output and its complete residual.
The original full input is pushed before the bounded inverse model is
multiplied. The native coefficientwise argument uses no normed-ring
instance, partition lower bound, or uniform finite-dimensional constant.
The original input L1 is supplied by its physical source construction. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.ProducedOutput
open Function MeasureTheory Lattice Wilson RG Marker MergeProof MergeProof.Accent
open LocalComparison Comparison.RG02 RG3.Script.Picnic
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {R : Census V}

omit [Fintype V] in
private theorem bounded_mul_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F M : Ω → Poly R}
    (hF : Integrable F μ) (hM : Envelope M) :
    Integrable (fun U => M U * F U) μ := by
  obtain ⟨B, hB⟩ := hM.cost
  apply integrable_pi_iff.mpr
  intro q
  change Integrable (fun U => (M U * F U).part q) μ
  simp_rw [Poly.part_mul]
  refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
  split
  · refine (((Poly.get b).restrictScalars ℝ).integrable_comp hF).bdd_mul (c := B)
      (((Poly.get a).continuous.measurable.comp hM.meas).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun U => (norm_le_pi_norm _ a).trans (hB U)
  · exact integrable_zero _ _ _

variable {C : Family G} {datum : LocalFormal.Datum C R}
    {D : V → ComparisonDensity.Address.Orbit}
    {fine : PhysicalCarrier C datum.cutoff datum.period (datum.level + 1)}
    {fineRoots : V → Site (C.side (datum.level + 1) datum.period)}
    {coarseRoots : V → Site (C.side datum.level datum.period)}
    {input : Taste (TestSpace D) fineRoots fine.rep R}
    (O : ProducedOutput D fine fineRoots coarseRoots input)

/-- The full original input L1 passes through the literal kernel to the
selected full output. No denominator or row-presentation equality is used. -/
theorem output_integrable (x : TestSpace D)
    (hI : Integrable (input.leaf x).density
      (prior G (C.side (datum.level + 1) datum.period))) :
    Integrable (O.output.leaf x).density
      (prior G (C.side datum.level datum.period)) := by
  rw [← O.density x]
  exact StepData.push_integrable
    (C.path.levels.transition_mass datum.level datum.period
      (C.path.β datum.cutoff datum.period (datum.level + 1))) _ hI

variable {Y : Bulk.Chain C.path}
    {inputColors : TestSpace D → Bulk.Colors R G (C.side (datum.level + 1) datum.period)}
    {order : ℕ} {p : BudgetPoint}
    {address : V → Support (C.side datum.level datum.period)}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood)
      (C.side datum.level datum.period)}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}

/-- The complete selected residual is the bounded inverse model times
the complete integrable output. Its original regular and forced channels
remain together, on exactly the chosen carrier. -/
theorem residual_integrable (hC : C.Makes)
    (hF : PrescribedPackets Y datum inputColors O.model order)
    (hP : O.model.Paid p address region w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
      width budget coverOffset coverSlope)
    (x : TestSpace D)
    (hI : Integrable (input.leaf x).density
      (prior G (C.side (datum.level + 1) datum.period))) :
    Integrable (O.residual.leaf x).density
      (prior G (C.side datum.level datum.period)) := by
  have hg : Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
      (datum.level + 1) ≠ 0 :=
    inv_ne_zero ((Real.sqrt_pos.2
      (Overlay.beta_positive hC.wilson (Nat.succ_le_of_lt datum.below))).ne')
  have hm := hF.inverse_multiplier_envelope hP hg x
  have he : (O.residual.leaf x).density = fun U =>
      Poly.pass (-(O.model.read x
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) U)) *
        (O.output.leaf x).density U := by
    funext U
    rw [O.full x U, ← mul_assoc,
      Next.Rank.Exponential.pass_neg _ (O.model.quiet_read x _ U), one_mul]
  rw [he]
  exact bounded_mul_integrable (O.output_integrable x hI) hm

/-- The selected native residual has the genuine L1 receipt required by
caption transport. The full RelativeBudget and its exact carrier threshold
are used only for the already-proved constant-caption identity. -/
theorem native_residual_integrable (hC : C.Makes)
    (hF : PrescribedPackets Y datum inputColors O.model order)
    (hP : O.model.Paid p address region w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
      width budget coverOffset coverSlope)
    {q : BudgetPoint} {radii cost : V → ℝ} {κ regularPrice forcedPrice : ℝ}
    (hB : RelativeBudget q O.residual radii κ (envelopeProduct cost)
      regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : q.threshold = O.carrier.rep.p.threshold)
    (x : TestSpace D)
    (hI : Integrable (input.leaf x).density
      (prior G (C.side (datum.level + 1) datum.period))) :
    Integrable (nativeResidual O.residual x)
      (prior G (C.side datum.level datum.period)) :=
  hB.nativeResidual_integrable hc ht x (O.residual_integrable hC hF hP x hI)

end YM.Integration.FullQLocal.ProducedOutput
end
