import YM.Integration.FullQLocalStrongTargetData
import YM.Integration.QLocalGradedVacuumLayers
import YM.Integration.FullQLocalRequestData

/-!
# Separate rendered input and analytic-output views

These records use an independent finite Request and numerical Schedule.
Positive support exponents are related by actual block geometry; analytic
width loss remains separate. The records preserve the original physical fields, independent tests,
whole-action authentication and exact calibration expression. Vacuum
geometry uses the conservative coefficient-zero-aware receipt; the leading
rank/coupling grading is explicit on the same unchanged layer list.

This is a data interface, not an existence theorem or an implication from
the old StrongJointTarget. That target and its original data remain
unchanged. PreparedInput is deliberately the analytically prepared strong
inlet; the complete weaker-stage domain and actual iterative re-admission
are separate duties. In particular an arbitrary produced output does not
automatically satisfy PreparedInput.

AnalyticOutput lists constructed conclusions. It must be selected from the
analytic input before physical perturbations, in the eventual joint theorem.
No output model, payment or formal identification is assumed by PreparedInput.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep

open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}

/-- The complete fine formal-action authentication depends only on the
finite order and independent test family, not on legacy support loss. -/
structure FineWholeAction (J : Request V) (datum : LocalFormal.Datum C R)
    (colors : TestSpace J.tests → Bulk.Colors R G
      (C.side (datum.level + 1) datum.period))
    (layers : List (Piece G (C.side (datum.level + 1) datum.period))) where
  standard x : (colors x).Standard
  input_summable (a : Piece G (C.side (datum.level + 1) datum.period))
      (ha : a ∈ layers) (U) :
    Summable (fun i : ℕ => a.packet.action i U)
  inputExtension : ℝ →
    Exterior.fieldDir G (C.side (datum.level + 1) datum.period) 1 → ℂ
  formalInputExtension : TestSpace J.tests → ℝ →
    Exterior.fieldDir G (C.side (datum.level + 1) datum.period) 1 → ℂ
  input_extension_value B : ∀ᶠ g : ℝ in 𝓝[>] 0,
    inputExtension g B =
      ((C.path.rep datum.cutoff datum.period (datum.level + 1)).path.inChannels
        (C.path.levels.params (datum.level + 1)).clip
        (C.path.levels.budget (datum.level + 1)) ((g ^ 2)⁻¹)
        (Precision.represent (g • B)) +
      unmaskedLayers (layers) g
        (Precision.represent (g • B)) : ℝ)
  formal_input_extension_value x B : ∀ᶠ g : ℝ in 𝓝[>] 0,
    formalInputExtension x g B =
      (Integral.localClassic g (Precision.represent (g • B)) (colors x)
        (C.path.levels.params (datum.level + 1)).clip
        (C.path.rep datum.cutoff datum.period (datum.level + 1)).path +
      Precision.loop (C.path.rep datum.cutoff datum.period (datum.level + 1)).path
        (Precision.represent (g • B)) : ℝ)
  input_extension_smooth B :
    ContDiffAt ℝ J.order (fun g : ℝ => inputExtension g B) 0
  formal_input_extension_smooth x B :
    ContDiffAt ℝ J.order (fun g : ℝ => formalInputExtension x g B) 0
  input_whole x B k (hk : k ≤ J.order) :
    ((k.factorial : ℝ)⁻¹) •
      iteratedFDeriv ℝ k (fun g : ℝ => inputExtension g B) 0 (fun _ => 1) =
    ((k.factorial : ℝ)⁻¹) •
      iteratedFDeriv ℝ k (fun g : ℝ => formalInputExtension x g B) 0 (fun _ => 1)

/-- The complete pre-reset formal action retains the same native ground
coefficient and scalar sequence on the chosen model. -/
structure WholeAction (Y : Bulk.Chain C.path) (J : Request V)
    (datum : LocalFormal.Datum C R)
    (colors : TestSpace J.tests → Bulk.Colors R G
      (C.side (datum.level + 1) datum.period))
    (P : Plan C datum.cutoff datum.period J.order) where
  standard x : (colors x).Standard
  input_summable (a : Piece G (C.side (datum.level + 1) datum.period))
      (ha : a ∈ P.layers (datum.level + 1)) (U) :
    Summable (fun i : ℕ => a.packet.action i U)
  inputExtension : ℝ →
    Exterior.fieldDir G (C.side (datum.level + 1) datum.period) 1 → ℂ
  formalInputExtension : TestSpace J.tests → ℝ →
    Exterior.fieldDir G (C.side (datum.level + 1) datum.period) 1 → ℂ
  input_extension_value B : ∀ᶠ g : ℝ in 𝓝[>] 0,
    inputExtension g B =
      ((C.path.rep datum.cutoff datum.period (datum.level + 1)).path.inChannels
        (C.path.levels.params (datum.level + 1)).clip
        (C.path.levels.budget (datum.level + 1)) ((g ^ 2)⁻¹)
        (Precision.represent (g • B)) +
      unmaskedLayers (P.layers (datum.level + 1)) g
        (Precision.represent (g • B)) : ℝ)
  formal_input_extension_value x B : ∀ᶠ g : ℝ in 𝓝[>] 0,
    formalInputExtension x g B =
      (Integral.localClassic g (Precision.represent (g • B)) (colors x)
        (C.path.levels.params (datum.level + 1)).clip
        (C.path.rep datum.cutoff datum.period (datum.level + 1)).path +
      Precision.loop (C.path.rep datum.cutoff datum.period (datum.level + 1)).path
        (Precision.represent (g • B)) : ℝ)
  input_extension_smooth B :
    ContDiffAt ℝ J.order (fun g : ℝ => inputExtension g B) 0
  formal_input_extension_smooth x B :
    ContDiffAt ℝ J.order (fun g : ℝ => formalInputExtension x g B) 0
  input_whole x B k (hk : k ≤ J.order) :
    ((k.factorial : ℝ)⁻¹) •
      iteratedFDeriv ℝ k (fun g : ℝ => inputExtension g B) 0 (fun _ => 1) =
    ((k.factorial : ℝ)⁻¹) •
      iteratedFDeriv ℝ k (fun g : ℝ => formalInputExtension x g B) 0 (fun _ => 1)
  extension : ℝ → Exterior.fieldDir G (C.side datum.level datum.period) 1 → ℂ
  scalar : ℕ → ℂ
  extension_value (B : Exterior.fieldDir G (C.side datum.level datum.period) 1) :
    ∀ᶠ g : ℝ in 𝓝[>] 0,
      extension g B =
        (modelAction P datum.level g (Precision.represent (g • B)) : ℂ)
  extension_smooth B : ContDiffAt ℝ J.order (fun g : ℝ => extension g B) 0
  output_whole (x : TestSpace J.tests) (B) (k : ℕ) (hk : k ≤ J.order) :
    ((k.factorial : ℝ)⁻¹) •
      iteratedFDeriv ℝ k (fun g : ℝ => extension g B) 0 (fun _ => 1) =
        Symmetry.Orbit.ground (datum.kernel Y) datum.forest datum.tag
          (colors x) J.order k B + scalar k

structure AnalyticInput (J : Request V) (A : Schedule C J)
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

variable {J : Request V} {A : Schedule C J} {datum : LocalFormal.Datum C R}

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

structure AnalyticOutput (caps : Handoff.OutputCapacities) (Y : Bulk.Chain C.path) (K : Prices A)
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


/-- Original startup suppliers retain every fine-action field under the
one-way finite-request projection. No new analytic hypothesis is inserted. -/
def FineWholeAction.fromLegacy {J : LocalComparison.Global.Setup V}
    {datum : LocalFormal.Datum C R}
    {colors : TestSpace J.tests → Bulk.Colors R G
      (C.side (datum.level + 1) datum.period)}
    {layers : List (Piece G (C.side (datum.level + 1) datum.period))}
    (H : Handoff.FineWholeAction J datum colors layers) :
    FineWholeAction (Request.fromLegacy J) datum colors layers where
  standard := H.standard
  input_summable := H.input_summable
  inputExtension := H.inputExtension
  formalInputExtension := H.formalInputExtension
  input_extension_value := H.input_extension_value
  formal_input_extension_value := H.formal_input_extension_value
  input_extension_smooth := H.input_extension_smooth
  formal_input_extension_smooth := H.formal_input_extension_smooth
  input_whole := H.input_whole

def WholeAction.fromLegacy {J : LocalComparison.Global.Setup V}
    {Y : Bulk.Chain C.path} {datum : LocalFormal.Datum C R}
    {colors : TestSpace J.tests → Bulk.Colors R G
      (C.side (datum.level + 1) datum.period)}
    {P : Plan C datum.cutoff datum.period J.order}
    (H : LocalComparison.Global.WholeAction Y J datum colors P) :
    WholeAction Y (Request.fromLegacy J) datum colors P where
  standard := H.standard
  input_summable := H.input_summable
  inputExtension := H.inputExtension
  formalInputExtension := H.formalInputExtension
  input_extension_value := H.input_extension_value
  formal_input_extension_value := H.formal_input_extension_value
  input_extension_smooth := H.input_extension_smooth
  formal_input_extension_smooth := H.formal_input_extension_smooth
  input_whole := H.input_whole
  extension := H.extension
  scalar := H.scalar
  extension_value := H.extension_value
  extension_smooth := H.extension_smooth
  output_whole := H.output_whole

end YM.Integration.FullQLocal.RenderedStep
end
