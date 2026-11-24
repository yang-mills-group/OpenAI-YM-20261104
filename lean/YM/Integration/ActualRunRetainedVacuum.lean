import YM.Integration.FullQLocalRetainedGrant
import YM.Integration.LocalComparisonVacuumCalibration
import YM.FullVolume.Cross

/-! Exact alpha-zero vacuum decomposition for the current retained output.
The selected raw source, actual coarse beta, complete render difference and
entire gas are preserved. The local source and packet receipts already imply
all summability used below. This is the pre-reset identity, not a construction
of an affine-null error or a paid calibration presentation. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunRetainedVacuum
open Function Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Classical BigOperators

variable {G : Gauge} (run : Run G)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} {A : NumericSchedule run.family J}
    {datum : LocalFormal.Datum run.family Gamma}
    {caps : Handoff.OutputCapacities} {Y : YM.Comparison.RG02.Bulk.Chain run.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : Real}
    {I : FullPreparedInputAt F eta_w}

/-- The same native coarse path and beta, with the selected list evaluated
at the actual coarse coupling. -/
def actualModel (M : AnalyticOutput caps Y K F)
    (U : Config G (run.family.side datum.level datum.period)) : Real :=
  (run.family.path.rep datum.cutoff datum.period datum.level).path.inChannels
    (run.family.path.levels.params datum.level).clip
    (run.family.path.levels.budget datum.level)
    (run.family.path.β datum.cutoff datum.period datum.level) U +
  Render.renders
    (Render.prefactor (Currency.g run.family datum.cutoff datum.period datum.level))
    (run.family.path.levels.budget datum.level) U (M.plan.layers datum.level)

variable {M : AnalyticOutput caps Y K F} (S : Retained.Chosen K I M)

/-- The complete discrepancy before the affine reset. In particular, the
raw source has not been declared affine-null or absorbed into a scalar. -/
def remainder (U : Config G (run.family.side datum.level datum.period)) : Real :=
  (S.vacuum.listing.read S.vacuum.source).additive
    (run.family.path.levels.budget datum.level) U +
  ((M.plan.predict datum.level -
      run.family.path.β datum.cutoff datum.period datum.level) *
    Push.BetaTransport.kinetic
      (run.family.path.rep datum.cutoff datum.period datum.level).path
      (run.family.path.levels.params datum.level).clip
      (run.family.path.levels.budget datum.level) U +
    Render.renders
      (Render.prefactor (Currency.gain (M.plan.predict datum.level)) -
        Render.prefactor (Currency.g run.family datum.cutoff datum.period datum.level))
      (run.family.path.levels.budget datum.level) U (M.plan.layers datum.level))

private theorem source_summable
    (U : Config G (run.family.side datum.level datum.period)) :
    Summable (fun i => (S.vacuum.listing.read S.vacuum.source).regularOccurrence
      (run.family.path.levels.budget datum.level) i U) := by
  have h := PreReset.series_of_EBound S.vacuum.estimate.unweighted U
  simpa only [Activities.regularOccurrence, (A.output_norm datum.level).threshold] using h

include S in
private theorem model_summable
    (a : Piece G (run.family.side datum.level datum.period))
    (ha : a ∈ M.plan.layers datum.level)
    (U : Config G (run.family.side datum.level datum.period)) :
    Summable (fun i => masked (run.family.path.levels.budget datum.level).threshold
      (a.packet.labels i).support (a.packet.action i) U) := by
  have h := PreReset.payload_series (M.output_layers_paid a ha)
    (S.vacuum.listing.read S.vacuum.source) U
  simpa only [(A.output_norm datum.level).threshold] using h

/-- The current retained record uses literal alpha=0, independently of any
Plan.alpha value. This identity holds on every original group field. -/
theorem exponent (U : Config G (run.family.side datum.level datum.period)) :
    S.output.carrier.rep.exponent U = S.output.carrier.rep.scalar -
      actualModel run M U - remainder run S U := by
  have hs : run.family.path.Conv datum.cutoff datum.period datum.level :=
    run.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le
  have hW : (run.family.path.rep datum.cutoff datum.period datum.level).path.Bounds
      (run.family.path.levels.params datum.level).clip
      (run.family.path.levels.params datum.level).width
      (run.family.path.levels.params datum.level).paths
      (run.family.path.levels.clock.loopCap datum.level) := by
    rw [← hs.clip]
    exact hs.good.paths
  have he := VacuumCalibration.raw_calibration_exponent
    (M.plan.layers datum.level)
    (run.family.path.rep datum.cutoff datum.period datum.level).path
    (run.family.path.levels.params datum.level).clip
    (run.family.path.levels.budget datum.level)
    S.vacuum.listing S.vacuum.source (M.plan.predict datum.level)
    S.vacuum.scalar 0 (run.family.path.β datum.cutoff datum.period datum.level)
    (Render.prefactor (Currency.gain (M.plan.predict datum.level)))
    (Render.prefactor (Currency.g run.family datum.cutoff datum.period datum.level))
    hW (source_summable run S) (model_summable run S) U
  simp only [sub_zero, zero_mul, add_zero] at he
  rw [S.vacuum.representation]
  unfold actualModel remainder
  exact he.trans (by ring)

/-- The entire selected gas remains in the full density; no healthy-field
restriction or rebooking of forced rows is used. -/
theorem density (U : Config G (run.family.side datum.level datum.period)) :
    S.output.carrier.rep.eval U =
      Real.exp (S.output.carrier.rep.scalar - actualModel run M U) *
        (Real.exp (-remainder run S U) *
          S.output.carrier.rep.activities.gas S.output.carrier.rep.p U) := by
  rw [Rep.eval, exponent run S U, sub_eq_add_neg, Real.exp_add, mul_assoc]

/-- The incoming vacuum attachment identifies this full expression with
the same Run's actual coarse vacuum, without equating internal Rep data. -/
theorem actual_density (hm : datum.level < datum.cutoff)
    (hFine : I.carrier.rep.eval =
      (run.family.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (U : Config G (run.family.side datum.level datum.period)) :
    (run.family.path.rep datum.cutoff datum.period datum.level).eval U =
      Real.exp (S.output.carrier.rep.scalar - actualModel run M U) *
        (Real.exp (-remainder run S U) *
          S.output.carrier.rep.activities.gas S.output.carrier.rep.p U) := by
  rw [← S.output.output_vacuum run.makes hm hFine]
  exact density run S U

end YM.Integration.ActualRunRetainedVacuum
end
