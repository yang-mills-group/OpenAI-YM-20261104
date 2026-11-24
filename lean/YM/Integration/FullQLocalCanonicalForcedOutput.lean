import YM.Integration.FullQLocalRetainedGrant
import YM.IterationFour.Vacuum.Reclose

/-!
The final canonical-output forced reserve in the full manuscript qlocal
conclusion. The complete family is chosen before projecting its legacy
family, so the reserve belongs to the identical selected source.

The native reset uses the original path, clipping, budget, selected listing,
selected source, scalar and complete selected layer list. Its full density
identity is supplied by the native reset/re-expression theorem separately.
This interface adds no Rates hypothesis and proves no calibration flatness.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep.Numeric.Canonical
open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {Gamma : Census V} {C : Family G}
    {J : Request V} {A : NumericSchedule C J}
    {caps : Handoff.OutputCapacities}

/-- The canonical reset of the exact selected pre-reset source, followed by
the entire original selected layer list, at the original native norm. -/
def reclosedRep {datum : LocalFormal.Datum C Gamma} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    (S : Retained.Chosen K I M) : Rep G (C.side datum.level datum.period) :=
  Render.append (M.plan.layers datum.level)
    (Reset.after
      (C.path.rep datum.cutoff datum.period datum.level).path
      (C.path.levels.params datum.level).clip
      (C.path.levels.budget datum.level)
      S.vacuum.listing S.vacuum.source
      (M.plan.predict datum.level) S.vacuum.scalar 0)
    (Render.prefactor (Currency.gain (M.plan.predict datum.level)))

/-- The final canonical output keeps the construction's native forced cap.
The norm and allowance are those of the original physical family. -/
def HasForcedReserve {datum : LocalFormal.Datum C Gamma} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    (S : Retained.Chosen K I M) : Prop :=
  (reclosedRep S).activities.KBound
    (C.path.levels.budget datum.level)
    (C.path.levels.clock.forcedAllowance datum.level)

/-- The final full marked representation promised after the canonical
attachments. Its rows live on that carrier's own forced family. This record
is not obtained by transporting old rows from scalar vacuum equality. -/
structure CanonicalOutput {datum : LocalFormal.Datum C Gamma} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    (S : Retained.Chosen K I M) where
  output : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input
  representation : output.carrier.rep = reclosedRep S
  same_model : output.model = M.model
  wellFormed : WellFormed (A.outputNorm datum.level) output.carrier.rep
  actual_forced : output.carrier.rep.activities.KBound
    (C.path.levels.budget datum.level) (C.path.levels.clock.forcedAllowance datum.level)
  fixed_forced : output.carrier.rep.activities.KBound
    (A.outputNorm datum.level) (C.path.levels.clock.forcedAllowance datum.level)
  output_active x : (output.output.leaf x).Active
  formal_active x : (output.formalAligned.leaf x).Active
  output_multilinear : Multilinear J.tests output.output
  formal_multilinear : Multilinear J.tests output.formalAligned
  residual_multilinear : Multilinear J.tests output.residual
  output_retains : FunctionalRetains output.output F.outputAddresses
  formal_retains : FunctionalRetains output.formalAligned F.outputAddresses
  residual_retains : FunctionalRetains output.residual F.outputAddresses
  aligned : QlocalMarkedPrimaryProposal.AlignedRegularRows
    output.output output.formalAligned output.residual
  primary : Retained.ChosenPrimary output

/-- The final representation has the full original input density, including
every mode. Both sides come from the same input and actual transition. -/
theorem CanonicalOutput.density_eq
    {datum : LocalFormal.Datum C Gamma} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {S : Retained.Chosen K I M} (P : CanonicalOutput S)
    (x : TestSpace J.tests) :
    (P.output.output.leaf x).density = (S.output.output.leaf x).density :=
  (P.output.density x).symm.trans (S.output.density x)

/-- Quantitative conclusions on the final canonical rows themselves.
The ordinary rate, divided forced rate, primary norm and conditional sharp
clause keep the full manuscript's original scales and quantifier order. -/
structure CanonicalBounds {datum : LocalFormal.Datum C Gamma} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {S : Retained.Chosen K I M} (P : CanonicalOutput S)
    (delta : ℝ) (forcedOrder : ℕ) where
  connected : Retained.ZeroChannels I → QlocalMarkedPrimaryProposal.IndependentConnectedClause J.tests
    (A.outputNorm datum.level) P.output.residual F.outputRadii
    (envelopeProduct F.kernelCosts)
    (markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited eta_w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
  residual_price : RelativeBudget (A.outputNorm datum.level)
    (pullback (testInclusion J.tests) P.output.residual) F.outputRadii
    (forcedDivisor C datum.level) (envelopeProduct F.kernelCosts)
    (Retained.ordinaryRate K I delta)
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
      forcedOrder)
  primary : P.primary.Bound
    (Retained.ordinaryRate K I delta)
  forced : ForcedBudget (A.outputNorm datum.level)
    (priceNormalized (envelopeProduct F.kernelCosts)
      (pullback (testInclusion J.tests) P.output.output)) F.outputRadii
    (forcedDivisor C datum.level)
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
      forcedOrder)


/-- The old pre-reset witness, canonical reserve and final marked output
are selected together. Later quantitative requests do not reselect rows. -/
structure CompleteFamily {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ}
    (models : Retained.ModelFamily (R := Gamma) caps Y J A floor n)
    (eta_w : ℕ → ℕ → ℕ → ℝ) where
  joint : Retained.JointFamily models eta_w
  reserve (datum : LocalFormal.Datum C Gamma) (hfirst : joint.first ≤ datum.level)
      (hfloors : Handoff.LocalFloors floor n datum)
      (hulls : Retained.ShortHulls models.prices datum) (F : AnalyticInput J A datum)
      (I : FullPreparedInputAt F (eta_w datum.cutoff datum.period datum.level))
      (intake : Retained.NativeIntake I) :
    HasForcedReserve (joint.select datum hfirst hfloors hulls F I intake)
  canonical (datum : LocalFormal.Datum C Gamma) (hfirst : joint.first ≤ datum.level)
      (hfloors : Handoff.LocalFloors floor n datum)
      (hulls : Retained.ShortHulls models.prices datum) (F : AnalyticInput J A datum)
      (I : FullPreparedInputAt F (eta_w datum.cutoff datum.period datum.level))
      (intake : Retained.NativeIntake I) :
    CanonicalOutput (joint.select datum hfirst hfloors hulls F I intake)
  canonical_bounds (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ later : ℕ, ∃ hlater : joint.first ≤ later,
      ∀ (datum : LocalFormal.Datum C Gamma) (hm : later ≤ datum.level)
        (hfloors : Handoff.LocalFloors floor n datum)
        (hulls : Retained.ShortHulls models.prices datum) (F : AnalyticInput J A datum)
        (I : FullPreparedInputAt F (eta_w datum.cutoff datum.period datum.level))
        (intake : Retained.NativeIntake I),
      Nonempty (CanonicalBounds
        (canonical datum (hlater.trans hm) hfloors hulls F I intake) delta forcedOrder)

/-- Explicit full-q hypothesis including the final forced-output conclusion.
The model, calibration-domain and later-bound quantifiers are unchanged. -/
structure CompleteGrant (caps : Handoff.OutputCapacities) (Y : Bulk.Chain C.path)
    (J : Request V) (A : NumericSchedule C J) (floor n : ℕ → ℕ)
    (pre : LocalComparison.Global.PreBlockConstant) where
  models : Retained.ModelFamily (R := Gamma) caps Y J A floor n
  vacuum_constant : models.prices.vacuumConstant = pre.value
  polynomial_degree : models.prices.polynomialDegree = pre.degree
  physical (eta_w : ℕ → ℕ → ℕ → ℝ)
      (flat : Retained.UniformlyFlat (C := C) J eta_w) :
    Nonempty (CompleteFamily models eta_w)

/-- Compatibility of hypotheses. The separately chosen legacy family of
this projection is not identified with the complete family's projection. -/
def CompleteGrant.forget {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ}
    {pre : LocalComparison.Global.PreBlockConstant}
    (H : CompleteGrant (Gamma := Gamma) caps Y J A floor n pre) :
    Retained.Grant (R := Gamma) caps Y J A floor n pre where
  models := H.models
  vacuum_constant := H.vacuum_constant
  polynomial_degree := H.polynomial_degree
  physical eta_w flat := by
    obtain ⟨family⟩ := H.physical eta_w flat
    exact ⟨family.joint⟩

/-- Choose the complete witness once; all applications use its joint field. -/
def CompleteGrant.family {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ}
    {pre : LocalComparison.Global.PreBlockConstant}
    (H : CompleteGrant (Gamma := Gamma) caps Y J A floor n pre)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := C) J eta_w) :
    CompleteFamily H.models eta_w :=
  Classical.choice (H.physical eta_w flat)

/-- Every later ordinary/forced bound and the canonical reserve refer to the
same output of the one complete family chosen before delta and forcedOrder. -/
theorem CompleteGrant.eventually_bounds {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ}
    {pre : LocalComparison.Global.PreBlockConstant}
    (H : CompleteGrant (Gamma := Gamma) caps Y J A floor n pre)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := C) J eta_w)
    (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ later : ℕ, ∃ hlater : (H.family eta_w flat).joint.first ≤ later,
      ∀ (datum : LocalFormal.Datum C Gamma) (hm : later ≤ datum.level)
        (hfloors : Handoff.LocalFloors floor n datum)
        (hulls : Retained.ShortHulls H.models.prices datum) (F : AnalyticInput J A datum)
        (I : FullPreparedInputAt F (eta_w datum.cutoff datum.period datum.level))
        (intake : Retained.NativeIntake I),
      HasForcedReserve ((H.family eta_w flat).joint.select datum (hlater.trans hm)
        hfloors hulls F I intake) ∧
      Nonempty (Retained.Bounds ((H.family eta_w flat).joint.select datum
        (hlater.trans hm) hfloors hulls F I intake) delta forcedOrder) := by
  obtain ⟨later, hlater, hbound⟩ := (H.family eta_w flat).joint.bounds
    delta hdelta forcedOrder
  refine ⟨later, hlater, ?_⟩
  intro datum hm hfloors hulls F I intake
  exact ⟨(H.family eta_w flat).reserve datum (hlater.trans hm) hfloors hulls F I intake,
    hbound datum hm hfloors hulls F I intake⟩

/-- The final rows are fixed before the ordinary and forced accuracy requests.
This is the bound carried by the assumed full-q witness, not a transport of
the old residual's bill through a changed forced-label set. -/
theorem CompleteGrant.eventually_canonical_bounds
    {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ}
    {pre : LocalComparison.Global.PreBlockConstant}
    (H : CompleteGrant (Gamma := Gamma) caps Y J A floor n pre)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := C) J eta_w)
    (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ later : ℕ, ∃ hlater : (H.family eta_w flat).joint.first ≤ later,
      ∀ (datum : LocalFormal.Datum C Gamma) (hm : later ≤ datum.level)
        (hfloors : Handoff.LocalFloors floor n datum)
        (hulls : Retained.ShortHulls H.models.prices datum) (F : AnalyticInput J A datum)
        (I : FullPreparedInputAt F (eta_w datum.cutoff datum.period datum.level))
        (intake : Retained.NativeIntake I),
      Nonempty (CanonicalBounds
        ((H.family eta_w flat).canonical datum (hlater.trans hm)
          hfloors hulls F I intake) delta forcedOrder) :=
  (H.family eta_w flat).canonical_bounds delta hdelta forcedOrder

end YM.Integration.FullQLocal.RenderedStep.Numeric.Canonical
end
