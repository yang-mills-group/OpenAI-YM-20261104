import YM.Integration.FullQLocalRenderedStepData
import YM.Integration.FullQLocalNumericSchedule

/-!
Numeric rendered input and output data on the preserved physical formulas.

These records reuse the original FineWholeAction and WholeAction classes.
Only the schedule parameter changes to NumericSchedule. Actual component
and marked-window admissibility must be constructed before any application;
this file states no selector, grant, existence theorem, or weak-domain closure.
The previous rendered records remain available in their original namespace.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep.Numeric

open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}

structure AnalyticInput (J : Request V) (A : NumericSchedule C J)
    (datum : LocalFormal.Datum C R) where
  whole_tests v : ∃ k w : ℕ, J.tests v = ⟨.whole, k, w⟩
  layers : List (Piece G (C.side (datum.level + 1) datum.period))
  layers_paid : Render.permits layers (A.inputNorm datum.level)
  vacuum : GradedVacuumLayers layers (A.inputNorm datum.level)
    J.order J.vacuumRankCap
    (A.inputWidth datum.level) (A.admittedCost datum.level)
  fineRoots : V → Site (C.side (datum.level + 1) datum.period)
  coarseRoots : V → Site (C.side datum.level datum.period)
  roots v : (C.path.levels.clock.op datum.level datum.period).ratio.parent
    (fineRoots v) = coarseRoots v
  colors : TestSpace J.tests → Bulk.Colors R G
    (C.side (datum.level + 1) datum.period)
  packets : MarkedPackets J.tests G (C.side (datum.level + 1) datum.period) R
  convention : InputColors colors packets
  rank_bounded : packets.rankCap ≤ J.inputPacketRankCap
  power_bounded : packets.powerCap ≤ J.inputPacketPowerCap
  whole_input : FineWholeAction J datum colors layers
  inputRadii : V → ℝ
  outputRadii : V → ℝ
  kernelCosts : V → ℝ
  input_radius_positive v : 0 < inputRadii v
  output_radius_positive v : 0 < outputRadii v
  kernel_positive v : 0 < kernelCosts v
  radius_admission v : outputRadii v * A.radiusLoss datum.level ≤ inputRadii v
  inputAddresses : V → Support (C.side (datum.level + 1) datum.period)
  input_origins v : fineRoots v ∈ inputAddresses v
  inputRegion : Comparison.Density.Testing.Region
    (fun v => (J.tests v).Mood) (C.side (datum.level + 1) datum.period)
  coverOffset : ℕ
  coverSlope : ℕ
  cover_cost : Real.exp ((A.inputNorm datum.level).supportExponent * coverOffset) ≤
    A.admittedCost datum.level
  input_paid : packets.Paid (A.inputNorm datum.level) inputAddresses inputRegion
    (fun v => inputRadii v / kernelCosts v)
    (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
    (A.inputWidth datum.level) (A.admittedCost datum.level) coverOffset coverSlope
  physical_period : J.physicalPeriodLower ≤ (C.S.period datum.period).val
  input_field_admitted : J.inputFieldOrder ≤
    (C.path.levels.budget (datum.level + 1)).order
  input_distance_admitted : J.inputDistanceOrder ≤
    (C.path.levels.budget (datum.level + 1)).power
  output_field_admitted : J.outputFieldOrder ≤ (C.path.levels.budget datum.level).order
  output_distance_admitted : J.outputDistanceOrder ≤ (C.path.levels.budget datum.level).power
  primary_admitted v : C.ref (J.outputWeight v) ≤ datum.level

variable {J : Request V} {A : NumericSchedule C J} {datum : LocalFormal.Datum C R}

def AnalyticInput.outputAddresses (F : AnalyticInput J A datum) (v : V) :
    Support (C.side datum.level datum.period) :=
  (F.inputAddresses v).image
    (C.path.levels.clock.op datum.level datum.period).ratio.parent

/-- This projection changes no row, coefficient, support or payment. -/
theorem AnalyticInput.grades (F : AnalyticInput J A datum) :
    Render.gradings F.layers J.order := F.vacuum.orders

structure PreparedInput (F : AnalyticInput J A datum) (eta_w : ℝ) where
  carrier : PhysicalCarrier C datum.cutoff datum.period (datum.level + 1)
  wellFormed : WellFormed (A.inputNorm datum.level) carrier.rep
  inherited : ℝ
  inherited_nonnegative : 0 ≤ inherited
  inherited_bound : inherited ≤ J.inheritedConstant *
    Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1) ^
      ((J.order : ℝ) + 1 - J.eta)
  error : Payload G (C.side (datum.level + 1) datum.period)
  error_paid : error.Invoice (A.inputNorm datum.level) inherited
  calibration : CalibrationPresentation carrier.rep (A.inputNorm datum.level) eta_w
  exponent U : carrier.rep.exponent U = carrier.rep.scalar -
    ((C.path.rep datum.cutoff datum.period (datum.level + 1)).path.inChannels
      carrier.rep.clip carrier.rep.p
      (C.path.β datum.cutoff datum.period (datum.level + 1)) U +
      Render.renders (Render.prefactor
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
        carrier.rep.p U F.layers) -
    error.amount (A.inputNorm datum.level) U - calibration.amount U
  input : Taste (TestSpace J.tests) F.fineRoots carrier.rep R
  multilinear : Multilinear J.tests input
  input_retains : FunctionalRetains input F.inputAddresses
  forcedPrice : ℝ
  forced_bound : forcedPrice ≤ J.forcedConstant
  prepared : LocalComparison.Global.Prepared datum.cutoff datum.period (datum.level + 1)
    (Handoff.legacyCarrier carrier) F.fineRoots input F.colors F.packets F.inputRadii
    (envelopeProduct F.kernelCosts) forcedPrice

structure AnalyticOutput (caps : Handoff.OutputCapacities) (Y : Bulk.Chain C.path) (K : NumericPrices A)
    (F : AnalyticInput J A datum) where
  model : MarkedPackets J.tests G (C.side datum.level datum.period) R
  prescribed : PrescribedPackets Y datum F.colors model J.order
  rank_bounded : model.rankCap ≤ caps.packetRank
  power_bounded : model.powerCap ≤ caps.packetPower
  plan : Plan C datum.cutoff datum.period J.order
  fine_layers : plan.layers (datum.level + 1) = F.layers
  whole_action : WholeAction Y J datum F.colors plan
  output_layers_paid : Render.permits (plan.layers datum.level) (A.outputNorm datum.level)
  vacuum : GradedVacuumLayers (plan.layers datum.level) (A.outputNorm datum.level)
    J.order caps.vacuumRank (A.outputWidth datum.level) (K.geometry datum.level)
  region : Comparison.Density.Testing.Region
    (fun v => (J.tests v).Mood) (C.side datum.level datum.period)
  coverOffset : ℕ
  coverSlope : ℕ
  cover_cost : Real.exp ((A.outputNorm datum.level).supportExponent * coverOffset) ≤
    K.geometry datum.level
  paid : model.Paid (A.outputNorm datum.level) F.outputAddresses region
    (fun v => F.outputRadii v / F.kernelCosts v)
    (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
    (A.outputWidth datum.level) (K.geometry datum.level) coverOffset coverSlope


end YM.Integration.FullQLocal.RenderedStep.Numeric
end
