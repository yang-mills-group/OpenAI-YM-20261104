import YM.Integration.FullQLocalRetainedOutput

/-!
The fixed-domain application projection of the one full manuscript qlocal
grant. Its existence is owed by that grant at the actually admitted original
family, component widths, finite capacities, floors and requested norms.
There is deliberately no assertion that every NumericSchedule has a Grant,
and no conversion from the preserved zero-channel StrongJointTarget.

Capacities and the pre-block constant are parameters selected before the
original lengths. Model selection precedes the calibration schedule and the
physical rough input. One joint output then precedes all later delta/order
requests. The strong native intake below is the actual-run application branch;
this module neither replaces nor purports to define the manuscript's other
weak-domain branch.

The final constructor consumes the returned full row budget, rather than a
second assumed majorant. It preserves the complete output and its residual.
A next AnalyticInput, native order admission, actual retuned read, and the
ordinary-price recurrence remain concrete construction obligations.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep.Numeric.Retained
open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}
    {J : Request V} {A : NumericSchedule C J}
    {caps : Handoff.OutputCapacities}

/-- The exact finite hull condition on the original torus. It does not assert
that an arbitrary native component construction fits those hulls. -/
structure ShortHulls (K : NumericPrices A)
    (datum : LocalFormal.Datum C R) : Prop where
  coarse (o : Site (C.side datum.level datum.period)) :
    Set.InjOn (fun z : Cover => o + wrap (C.side datum.level datum.period) z)
      (↑(box (K.hullMultiplier datum.level *
        (1 + C.path.levels.clock.coverSize datum.level))) : Set Cover)
  fine (o : Site (C.side (datum.level + 1) datum.period)) :
    Set.InjOn (fun z : Cover => o + wrap (C.side (datum.level + 1) datum.period) z)
      (↑(box (K.hullMultiplier datum.level *
        (1 + C.path.levels.clock.coverSize (datum.level + 1)))) : Set Cover)

def UniformlyFlat (J : Request V) (eta_w : ℕ → ℕ → ℕ → ℝ) : Prop :=
  (∀ N p m, m < N → J.physicalPeriodLower ≤ (C.S.period p).val → 0 ≤ eta_w N p m) ∧
  ∀ q : ℕ, ∃ first : ℕ, ∀ N p m, first ≤ m → m < N →
    J.physicalPeriodLower ≤ (C.S.period p).val →
    eta_w N p m ≤ (Pert.Asymptotics.regulatorRun C N p (m + 1)) ^ q

/-- These are the genuine analytic models. The rough marked input is not an
argument, and no analyticity of that rough input is requested. -/
structure ModelFamily (caps : Handoff.OutputCapacities) (Y : Bulk.Chain C.path)
    (J : Request V) (A : NumericSchedule C J) (floor n : ℕ → ℕ) where
  prices : NumericPrices A
  first : ℕ
  realize (datum : LocalFormal.Datum C R) (hfirst : first ≤ datum.level)
    (hfloors : Handoff.LocalFloors floor n datum)
    (hulls : ShortHulls prices datum) (F : AnalyticInput J A datum) :
      AnalyticOutput caps Y prices F

/-- The returned carrier and every full marked row are selected once. The
ordinary input price is the accumulated actual state and is never identified
with the fresh analytic markedRate. -/
structure JointFamily {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ}
    (M : ModelFamily (R := R) caps Y J A floor n)
    (eta_w : ℕ → ℕ → ℕ → ℝ) where
  first : ℕ
  after_model : M.first ≤ first
  select (datum : LocalFormal.Datum C R) (hfirst : first ≤ datum.level)
    (hfloors : Handoff.LocalFloors floor n datum) (hulls : ShortHulls M.prices datum)
    (F : AnalyticInput J A datum)
    (I : FullPreparedInputAt F (eta_w datum.cutoff datum.period datum.level))
    (intake : NativeIntake I) :
      Chosen M.prices I (M.realize datum (after_model.trans hfirst) hfloors hulls F)
  bounds (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ later : ℕ, ∃ hlater : first ≤ later,
      ∀ (datum : LocalFormal.Datum C R) (hm : later ≤ datum.level)
        (hfloors : Handoff.LocalFloors floor n datum)
        (hulls : ShortHulls M.prices datum) (F : AnalyticInput J A datum)
        (I : FullPreparedInputAt F (eta_w datum.cutoff datum.period datum.level))
        (intake : NativeIntake I),
      Nonempty (Bounds (select datum (hlater.trans hm) hfloors hulls F I intake)
        delta forcedOrder)

/-- One full-q parameter, already applied at its genuine native domain.
The externally fixed capacities/constants retain their pre-length position.
This record is not asserted to exist for arbitrary numerical data. -/
structure Grant (caps : Handoff.OutputCapacities) (Y : Bulk.Chain C.path)
    (J : Request V) (A : NumericSchedule C J) (floor n : ℕ → ℕ)
    (pre : PreBlockConstant) where
  models : ModelFamily (R := R) caps Y J A floor n
  vacuum_constant : models.prices.vacuumConstant = pre.value
  polynomial_degree : models.prices.polynomialDegree = pre.degree
  physical (eta_w : ℕ → ℕ → ℕ → ℝ)
    (flat : UniformlyFlat (C := C) J eta_w) :
      Nonempty (JointFamily models eta_w)

/-- Choose the same family before any delta or forced-order request. -/
def Grant.family {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ}
    {pre : PreBlockConstant} (H : Grant (R := R) caps Y J A floor n pre)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : UniformlyFlat (C := C) J eta_w) :
    JointFamily H.models eta_w :=
  Classical.choice (H.physical eta_w flat)

/-- The one grant supplies all later bounds for that same chosen family. -/
theorem Grant.eventually_bounds {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ}
    {pre : PreBlockConstant} (H : Grant (R := R) caps Y J A floor n pre)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : UniformlyFlat (C := C) J eta_w)
    (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ later : ℕ, ∃ hlater : (H.family eta_w flat).first ≤ later,
      ∀ (datum : LocalFormal.Datum C R) (hm : later ≤ datum.level)
        (hfloors : Handoff.LocalFloors floor n datum)
        (hulls : ShortHulls H.models.prices datum) (F : AnalyticInput J A datum)
        (I : FullPreparedInputAt F (eta_w datum.cutoff datum.period datum.level))
        (intake : NativeIntake I),
      Nonempty (Bounds ((H.family eta_w flat).select datum (hlater.trans hm)
        hfloors hulls F I intake) delta forcedOrder) :=
  (H.family eta_w flat).bounds delta hdelta forcedOrder

variable {datum : LocalFormal.Datum C R} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}

/-- The returned full rough budget is the next preparation's budget.
The actual retuned packet and its all-test read still have to be constructed.
The paying norm here is exactly the returned output norm, with no enlargement
to the growing native-stage derivative norm. -/
def Chosen.prepareNext (S : Chosen K I M) {delta : ℝ} {forcedOrder : ℕ}
    (bound : Bounds S delta forcedOrder)
    (colors : TestSpace J.tests → Bulk.Colors R G (C.side datum.level datum.period))
    (packets : MarkedPackets J.tests G (C.side datum.level datum.period) R)
    (hColors : InputColors colors packets)
    (hRead : ∀ x U,
      packets.read x (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
        datum.level) U =
      S.output.model.read x (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
        (datum.level + 1)) U) :
    PreparedWithRemainderAt datum.cutoff datum.period datum.level
      (A.outputNorm datum.level) (Handoff.legacyCarrier S.output.carrier)
      F.coarseRoots S.output.output colors packets F.outputRadii
      (envelopeProduct F.kernelCosts) (ordinaryRate K I delta)
      ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
        (datum.level + 1)) ^ forcedOrder) :=
  Numeric.prepareProduced S.output (A.outputNorm datum.level) colors packets
    F.outputRadii F.kernelCosts (ordinaryRate K I delta)
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
      (datum.level + 1)) ^ forcedOrder) hColors hRead bound.residual_price

end YM.Integration.FullQLocal.RenderedStep.Numeric.Retained
end
