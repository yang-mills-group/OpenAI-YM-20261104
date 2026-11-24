import YM.Integration.WilsonLimitConstruction.FundedCanonicalInputPayload
import YM.Integration.NativeKineticCalibration

/-! The actual scalar and the full uniform-field calibration price of the
reclosed native source, with its original clip and signed rep. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedCanonicalCalibration

open Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    {J : Request V} (R : Run G) {d : LocalFormal.Datum R.family Γ}
    {A : NumericSchedule R.family J} {K : NumericPrices A} {F : AnalyticInput J A d}
    {η : ℝ} {I : FullPreparedInputAt F η} {M : FundedRenderedBank.Catalogue J d}
    {S : FundedRenderedBank.Chosen K I M} (P : FundedRenderedBank.Canonical S)

theorem parameters : P.bank.output.carrier.rep.beta = M.plan.predict d.level +
    Averaging.delta (S.vacuum.listing.read S.vacuum.source) ∧
    P.bank.output.carrier.rep.v = vac S.vacuum.source S.vacuum.scalar := by
  constructor
  · rw [P.representation]
    change M.plan.predict d.level + 0 + Averaging.delta (S.vacuum.listing.read S.vacuum.source) = _
    simp
  · rw [P.representation]
    rfl

theorem actual_eval (hFine : I.carrier.rep.eval =
    (R.family.path.rep d.cutoff d.period (d.level+1)).eval) :
    P.bank.output.carrier.rep.eval = (R.family.path.rep d.cutoff d.period d.level).eval :=
  P.bank.output.output_vacuum R.makes d.below hFine

def defect : ℝ :=
  P.bank.output.carrier.rep.beta - R.family.path.β d.cutoff d.period d.level

def charge (p : BudgetPoint) : ℝ :=
  NativeKineticCalibration.price G (R.family.path.levels.params d.level).clip p
    (R.family.path.levels.params d.level).width (R.family.path.levels.params d.level).paths (defect R P)

theorem measured (p : BudgetPoint) (hnorm : p = A.outputNorm d.level)
    (hw : Geo.Width (A.outputNorm d.level) (R.family.path.levels.params d.level).clip
      (R.family.path.levels.params d.level).width) :
    ∃ C : CalibrationPresentation P.bank.output.carrier.rep p (charge R P p),
      ∀ U, C.amount U = defect R P * Push.BetaTransport.kinetic
        (R.family.path.rep d.cutoff d.period d.level).path
        (R.family.path.levels.params d.level).clip p U := by
  subst p
  have ht : (A.outputNorm d.level).threshold = P.bank.output.carrier.rep.p.threshold := by
    rw [P.representation]
    exact (A.output_norm d.level).threshold
  let D := FundedCanonicalInputPayload.path_bounds R (datum := d)
  let HD := FundedCanonicalInputPayload.decent R (A := A) (datum := d)
  exact ⟨NativeKineticCalibration.calibration D HD hw P.bank.output.carrier.rep ht (defect R P),
    NativeKineticCalibration.amount D HD hw P.bank.output.carrier.rep ht (defect R P)⟩

end YM.Integration.WilsonLimitConstruction.FundedCanonicalCalibration
end
