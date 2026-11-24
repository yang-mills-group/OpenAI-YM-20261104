import YM.Integration.ActualRunRetainedVacuum
import YM.Integration.GradedVacuumLayerRescaling

/-!
# The current selected vacuum with its renderer moved to the actual coupling

The ratio and layer list are defined from the same selected M and original
Run. The full renderer difference is absorbed by the exact coefficient map;
the true predictor-minus-actual kinetic difference remains in the residual.
No beta equality, affine reset or smallness estimate is asserted.

The density identity needs no positivity of the selected predictor. The
complete graded receipt is stated separately and visibly requires predictor
positivity, whose actual same-M purchase is not supplied by this module.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunRetunedVacuum

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
    {caps : Handoff.OutputCapacities}
    {Y : YM.Comparison.RG02.Bulk.Chain run.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : Real}
    {I : FullPreparedInputAt F eta_w}

/-- Fixed once the original datum and selected Plan have been fixed. -/
def ratio (M : AnalyticOutput caps Y K F) : ℝ :=
  Currency.gain (M.plan.predict datum.level) /
    Currency.g run.family datum.cutoff datum.period datum.level

def retunedLayers (M : AnalyticOutput caps Y K F) :
    List (Piece G (run.family.side datum.level datum.period)) :=
  NativeVacuumLayerRescaling.layers (ratio run M) (M.plan.layers datum.level)

/-- The same original native coarse path and beta, now with the literal
rescaled layer list at the actual coarse regulator. -/
def model (M : AnalyticOutput caps Y K F)
    (U : Config G (run.family.side datum.level datum.period)) : ℝ :=
  (run.family.path.rep datum.cutoff datum.period datum.level).path.inChannels
    (run.family.path.levels.params datum.level).clip
    (run.family.path.levels.budget datum.level)
    (run.family.path.β datum.cutoff datum.period datum.level) U +
  Render.renders
    (Render.prefactor (Currency.g run.family datum.cutoff datum.period datum.level))
    (run.family.path.levels.budget datum.level) U (retunedLayers run M)

variable {M : AnalyticOutput caps Y K F} (S : Retained.Chosen K I M)

/-- The true kinetic correction remains. No affine-nullness is inferred. -/
def remainder (U : Config G (run.family.side datum.level datum.period)) : ℝ :=
  (S.vacuum.listing.read S.vacuum.source).additive
    (run.family.path.levels.budget datum.level) U +
  (M.plan.predict datum.level -
      run.family.path.β datum.cutoff datum.period datum.level) *
    Push.BetaTransport.kinetic
      (run.family.path.rep datum.cutoff datum.period datum.level).path
      (run.family.path.levels.params datum.level).clip
      (run.family.path.levels.budget datum.level) U

/-- All original masks and group fields are retained by the exact map. -/
theorem rendered (U : Config G (run.family.side datum.level datum.period)) :
    Render.renders
      (Render.prefactor (Currency.g run.family datum.cutoff datum.period datum.level))
      (run.family.path.levels.budget datum.level) U (retunedLayers run M) =
    Render.renders (Render.prefactor (Currency.gain (M.plan.predict datum.level)))
      (run.family.path.levels.budget datum.level) U (M.plan.layers datum.level) := by
  have hg : 0 < Currency.g run.family datum.cutoff datum.period datum.level :=
    Currency.g_pos run.makes datum.cutoff datum.period datum.level datum.below.le
  unfold retunedLayers
  rw [NativeVacuumLayerRescaling.renders]
  unfold ratio
  rw [div_mul_cancel₀ _ hg.ne']

theorem exponent (U : Config G (run.family.side datum.level datum.period)) :
    S.output.carrier.rep.exponent U =
      S.output.carrier.rep.scalar - model run M U - remainder run S U := by
  rw [ActualRunRetainedVacuum.exponent run S U]
  unfold ActualRunRetainedVacuum.actualModel ActualRunRetainedVacuum.remainder
  unfold model remainder
  rw [Render.render_sub, rendered run (M := M) U]
  ring

theorem density (U : Config G (run.family.side datum.level datum.period)) :
    S.output.carrier.rep.eval U =
      Real.exp (S.output.carrier.rep.scalar - model run M U) *
        (Real.exp (-remainder run S U) *
          S.output.carrier.rep.activities.gas S.output.carrier.rep.p U) := by
  rw [Rep.eval, exponent run S U, sub_eq_add_neg, Real.exp_add, mul_assoc]

theorem actual_density
    (hFine : I.carrier.rep.eval =
      (run.family.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (U : Config G (run.family.side datum.level datum.period)) :
    (run.family.path.rep datum.cutoff datum.period datum.level).eval U =
      Real.exp (S.output.carrier.rep.scalar - model run M U) *
        (Real.exp (-remainder run S U) *
          S.output.carrier.rep.activities.gas S.output.carrier.rep.p U) := by
  rw [← S.output.output_vacuum run.makes datum.below hFine]
  exact density run S U

/-- Structural permits hold independently of any numerical ratio bound. -/
theorem permits : Render.permits (retunedLayers run M) (A.outputNorm datum.level) :=
  NativeVacuumLayerRescaling.permits M.output_layers_paid (ratio run M)

/-- This hypothesis is deliberately separate from the unconditional density
identity. No existing retained Grant field is claimed to supply it. -/
theorem ratio_pos (hPredict : 0 < M.plan.predict datum.level) : 0 < ratio run M := by
  exact div_pos (inv_pos.mpr (Real.sqrt_pos.2 hPredict))
    (Currency.g_pos run.makes datum.cutoff datum.period datum.level datum.below.le)

/-- Full original graded data, with its explicit ratio-dependent enlargement.
The original norm, rank cap, width, cover constants and all atoms survive. -/
def graded (hPredict : 0 < M.plan.predict datum.level) :
    GradedVacuumLayers (retunedLayers run M) (A.outputNorm datum.level)
      J.order caps.vacuumRank (A.outputWidth datum.level)
      (NativeVacuumLayerRescaling.factorBound (ratio run M) J.order *
        K.geometry datum.level) :=
  GradedVacuumLayerRescaling.graded M.vacuum (ratio_pos run hPredict)

end YM.Integration.ActualRunRetunedVacuum
end
