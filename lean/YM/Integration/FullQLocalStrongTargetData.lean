import YM.Integration.LocalComparisonGlobalContract
import YM.Integration.FullQLocalStrongApplication
import YM.Integration.FullQLocalProducedOutput
import YM.Integration.LocalComparisonCalibrationClass
import YM.Integration.QlocalMarkedPrimaryProposal

/-!
# Conditional data for the strong local comparison

`StrongJointTarget` states the comparison for a strong, analytically
prepared input. Extending it to the full weak-stage domain and supplying
the complete native component-width construction require further data.
This module defines the target proposition and the input and output records.

The imported global comparison provides the concrete norm, packet,
pre-reset and price definitions. The input hypotheses use the fine-action
data. Output realization, payment and whole-action correspondence are
conclusions. Model realization precedes the physical perturbations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FullQLocal.Handoff
open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}

/-- The fine half of the whole-action authentication. There is no coarse
extension, prescribed output coefficient or output payment in this record. -/
structure FineWholeAction (J : Setup V) (datum : LocalFormal.Datum C R)
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

/-- Derived output capacities are selected from the fixed finite request,
before widths, blocks, and physical perturbations. They need not equal the
incoming degree bounds. -/
structure OutputCapacities where
  vacuumRank : ℕ
  packetRank : ℕ
  packetPower : ℕ

variable {caps : OutputCapacities}

/-- Fixed analytic data. The physical vacuum/error/gas to which the theorem
is applied is deliberately absent. Output radii are requested numerical data;
the output region, packet rendering and its payment are produced later. -/
structure AnalyticDatum (J : Setup V) (A : Admission C J)
    (datum : LocalFormal.Datum C R) where
  whole_tests v : ∃ k w : ℕ, J.tests v = ⟨.whole, k, w⟩
  layers : List (Piece G (C.side (datum.level + 1) datum.period))
  grades : Render.gradings layers J.order
  layers_paid : Render.permits layers (A.inputNorm datum.level)
  analytic : VacuumPackets layers (A.inputNorm datum.level) J.vacuumRankCap
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

variable {J : Setup V} {A : Admission C J} {datum : LocalFormal.Datum C R}

def AnalyticDatum.outputAddresses (F : AnalyticDatum J A datum) (v : V) :
    Support (C.side datum.level datum.period) :=
  (F.inputAddresses v).image
    (C.path.levels.clock.op datum.level datum.period).ratio.parent

def legacyCarrier {N p m : ℕ} (Q : PhysicalCarrier C N p m) :
    LocalComparison.Global.StepCarrier C N p m :=
  ⟨Q.rep, Q.path, Q.clip, Q.point⟩

/-- Physical perturbations of the already fixed analytic input. Full original
K rows and predicates remain inside `carrier.rep`; calibration.amount is in
the exact exponent, including all failed-mask/clip terms. -/
structure PhysicalInput (F : AnalyticDatum J A datum) (eta_w : ℝ) where
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
    (legacyCarrier carrier) F.fineRoots input F.colors F.packets F.inputRadii
    (envelopeProduct F.kernelCosts) forcedPrice

/-- Explicit strong inlet only. This is not a renamed weak-stage predicate. -/
structure StrongInput {F : AnalyticDatum J A datum} {eta_w : ℝ}
    (I : PhysicalInput F eta_w) : Prop where
  original : I.carrier.rep.activities.KBound
    (C.path.levels.budget (datum.level + 1))
    (C.path.levels.clock.forcedAllowance (datum.level + 1))
  reserved : I.carrier.rep.activities.KBound (A.inputNorm datum.level)
    (C.path.levels.clock.forcedAllowance (datum.level + 1))

/-- The model is realized from analytic data before any PhysicalInput. Thus
neither its completion nor its coarse coefficients can be fitted to that
physical error. All output payment and whole-action facts are conclusions. -/
structure RealizedModel (caps : OutputCapacities) (Y : Bulk.Chain C.path) (K : Prices A)
    (F : AnalyticDatum J A datum) where
  model : MarkedPackets J.tests G (C.side datum.level datum.period) R
  prescribed : PrescribedPackets Y datum F.colors model J.order
  rank_bounded : model.rankCap ≤ caps.packetRank
  power_bounded : model.powerCap ≤ caps.packetPower
  plan : Plan C datum.cutoff datum.period J.order
  fine_layers : plan.layers (datum.level + 1) = F.layers
  whole_action : WholeAction Y J datum F.colors plan
  output_layers_paid : Render.permits (plan.layers datum.level) (A.outputNorm datum.level)
  analytic_output : VacuumPackets (plan.layers datum.level) (A.outputNorm datum.level)
    caps.vacuumRank (A.outputWidth datum.level) (K.geometry datum.level)
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

/-- Primary data is one complete functional on the already chosen output. -/
structure ChosenPrimary {F : AnalyticDatum J A datum} {eta_w : ℝ}
    {I : PhysicalInput F eta_w}
    (O : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input) where
  coefficient : (v : V) → TestSpace J.tests →
    Source.Coefficient (C.labels.level (J.outputWeight v))
      (C.side datum.level datum.period)
  support v x y : (coefficient v x).support = (coefficient v y).support
  format v x : (coefficient v x).Format (F.coarseRoots v) C.params O.carrier.rep
  remainder v x : ∃ k r, (coefficient v x).remBound (F.coarseRoots v) O.carrier.rep k r
  singleton v x U : (coefficient v x).density (F.coarseRoots v)
    (C.localSection (J.outputWeight v)) O.carrier.rep U =
      ((O.output.leaf x).density U).part (R.fire v)

def ChosenPrimary.Bound {F : AnalyticDatum J A datum} {eta_w : ℝ}
    {I : PhysicalInput F eta_w}
    {O : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input}
    (P : ChosenPrimary O) (price : ℝ) : Prop :=
  ∀ (v : V) (x : IndependentTests J.tests),
    (F.outputRadii v / F.kernelCosts v) *
      (C.labels.level (J.outputWeight v)).coeffSize
        (Trace.Physical.Germ.projection (C.labels.level (J.outputWeight v)) C.params
          O.carrier.rep.p.threshold (F.coarseRoots v)
          (P.coefficient v (testInclusion J.tests x)) -
        Trace.Physical.Germ.vector (C.labels.level (J.outputWeight v)) C.params
          O.carrier.rep.p.threshold (F.coarseRoots v)
          (fun U => (O.model.read (testInclusion J.tests x)
            (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
              (datum.level + 1)) U).part (R.fire v))) ≤ price

/-- The native pre-reset source and its bound use the same produced carrier.
No older-error kinetic correction is extracted here: alpha is literally zero,
and every such contribution remains inside the bounded raw source. A later
scalar/coupling reset and its exact costs belong to the downstream application. -/
structure ChosenVacuum {Y : Bulk.Chain C.path} (K : Prices A)
    {F : AnalyticDatum J A datum} {eta_w : ℝ} (I : PhysicalInput F eta_w)
    (M : RealizedModel caps Y K F)
    (O : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input) where
  listing : AnalyticBridge.VerifiedReset.Collection.Listing G
    (C.side datum.level datum.period)
  source : AnalyticBridge.VerifiedReset.Collection.Source G
    (C.side datum.level datum.period)
  scalar : ℝ
  estimate : AnalyticBridge.VerifiedReset.Collection.Local listing
    (A.outputNorm datum.level) source
    (vacuumRate J.order K.vacuumConstant (C.S.block datum.level).val
      (K.vanishing datum.level) (K.geometry datum.level) I.inherited eta_w
      (Currency.g C datum.cutoff datum.period (datum.level + 1)))
    (C.path.levels.clock.forcedAllowance datum.level)
  representation : O.carrier.rep =
    PreReset.append (M.plan.layers datum.level)
      (C.path.rep datum.cutoff datum.period datum.level).path
      (C.path.levels.params datum.level).clip (C.path.levels.budget datum.level)
      listing source (M.plan.predict datum.level) scalar 0
      (Render.prefactor (Currency.gain (M.plan.predict datum.level)))

/-- One complete joint witness. The chosen model is fixed before I; the
vacuum, formal companion, aligned residual and primary precede delta and A. -/
structure Chosen {Y : Bulk.Chain C.path} (K : Prices A)
    {F : AnalyticDatum J A datum} {eta_w : ℝ} (I : PhysicalInput F eta_w)
    (M : RealizedModel caps Y K F) where
  output : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input
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
  vacuum : ChosenVacuum K I M output
  primary : ChosenPrimary output

/-- Only estimates/majorants vary with the later requests. The exact max norm
and the native factorial currency are stated separately on the same residual;
no definitional equality between those norms is asserted. -/
structure Bounds {Y : Bulk.Chain C.path} {K : Prices A}
    {F : AnalyticDatum J A datum} {eta_w : ℝ} {I : PhysicalInput F eta_w}
    {M : RealizedModel caps Y K F} (S : Chosen K I M) (delta : ℝ) (forcedOrder : ℕ) where
  connected : QlocalMarkedPrimaryProposal.IndependentConnectedClause J.tests
    (A.outputNorm datum.level) S.output.residual F.outputRadii
    (envelopeProduct F.kernelCosts)
    (markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited eta_w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
  residual_price : RelativeBudget (A.outputNorm datum.level)
    (pullback (testInclusion J.tests) S.output.residual) F.outputRadii
    (forcedDivisor C datum.level) (envelopeProduct F.kernelCosts)
    (markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited eta_w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
      forcedOrder)
  primary : S.primary.Bound
    (markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited eta_w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
  forced : ForcedBudget (A.outputNorm datum.level)
    (priceNormalized (envelopeProduct F.kernelCosts)
      (pullback (testInclusion J.tests) S.output.output)) F.outputRadii
    (forcedDivisor C datum.level)
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
      forcedOrder)

/-- Uniformity is over the original cutoff/period domain at a late stage.
This does not choose a different representation at a requested power. -/
def UniformlyFlat (J : Setup V) (eta_w : ℕ → ℕ → ℕ → ℝ) : Prop :=
  (∀ N p m, m < N → J.physicalPeriodLower ≤ (C.S.period p).val → 0 ≤ eta_w N p m) ∧
  ∀ q : ℕ, ∃ first : ℕ, ∀ N p m, first ≤ m → m < N →
    J.physicalPeriodLower ≤ (C.S.period p).val →
    eta_w N p m ≤ (Pert.Asymptotics.regulatorRun C N p (m + 1)) ^ q

/-- Additional finite-request floors are local at both actual profiles.
The original Sheet floor is retained globally by the enclosing target. -/
def LocalFloors (floor n : ℕ → ℕ) (datum : LocalFormal.Datum C R) : Prop :=
  floor (C.path.levels.clock.J datum.level) ≤ n (C.path.levels.clock.J datum.level) ∧
  floor (C.path.levels.clock.J (datum.level + 1)) ≤
    n (C.path.levels.clock.J (datum.level + 1))

/-- Analytic models and their common prices are selected before the entire
calibration-size schedule, as well as before every physical input. -/
structure ModelFamily (caps : OutputCapacities) (Y : Bulk.Chain C.path)
    (J : Setup V) (A : Admission C J) (floor n : ℕ → ℕ) where
  prices : Prices A
  first : ℕ
  realize (datum : LocalFormal.Datum C R) (hfirst : first ≤ datum.level)
    (hfloors : LocalFloors floor n datum) (hulls : ShortHulls prices datum)
    (F : AnalyticDatum J A datum) : RealizedModel caps Y prices F

/-- One physical family for a fixed calibration schedule. Its later requests
change only thresholds and majorants, never its chosen output. -/
structure JointFamily {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ}
    (M : ModelFamily (R := R) caps Y J A floor n)
    (eta_w : ℕ → ℕ → ℕ → ℝ) where
  first : ℕ
  after_model : M.first ≤ first
  select (datum : LocalFormal.Datum C R) (hfirst : first ≤ datum.level)
    (hfloors : LocalFloors floor n datum) (hulls : ShortHulls M.prices datum)
    (F : AnalyticDatum J A datum)
    (I : PhysicalInput F (eta_w datum.cutoff datum.period datum.level))
    (intake : StrongInput I) :
      Chosen M.prices I (M.realize datum (after_model.trans hfirst) hfloors hulls F)
  bounds (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ later : ℕ, ∃ hlater : first ≤ later,
      ∀ (datum : LocalFormal.Datum C R) (hm : later ≤ datum.level)
        (hfloors : LocalFloors floor n datum) (hulls : ShortHulls M.prices datum)
        (F : AnalyticDatum J A datum)
        (I : PhysicalInput F (eta_w datum.cutoff datum.period datum.level))
        (intake : StrongInput I),
      Nonempty (Bounds (select datum (hlater.trans hm) hfloors hulls F I intake)
        delta forcedOrder)

/-- FIRST STRONG CANDIDATE ONLY. The complete weak-stage predicate and the
full original component-width dictionary remain specification obligations.
The numerical width receipt here is not claimed to settle those obligations.
This proposition is an explicit proof target, never a certified assumption. -/
def StrongJointTarget : Prop :=
  G.Simple → ∀ (V : Type) [DecidableEq V] [Fintype V] (R : Census V)
    (s : RG.Supply.Sheet G) (J : Setup V),
    ∃ caps : OutputCapacities,
      ∃ W : ProfileWidths, (∀ i, W.width i ≤ (s.profile i).width) ∧
        ∃ floor : ℕ → ℕ, s.floorL ≤ floor ∧
          ∃ K : PreBlockConstant,
            ∀ (n : ℕ → ℕ), s.floorL ≤ n → ∀ (C : Family G) (Y : Bulk.Chain C.path),
              Y.preCosts = PhysicalNext.ThroughLaunch.raise s n → C.Makes →
              WidthPayment C W → ∀ A : Admission C (onFamily J W C),
              ∃ M : ModelFamily (R := R) caps Y (onFamily J W C) A floor n,
                M.prices.vacuumConstant = K.value ∧
                M.prices.polynomialDegree = K.degree ∧
                ∀ eta_w : ℕ → ℕ → ℕ → ℝ, UniformlyFlat (C := C) J eta_w →
                  Nonempty (JointFamily M eta_w)

end YM.Integration.FullQLocal.Handoff
end
