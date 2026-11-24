import YM.Integration.LocalComparisonReclosure
import YM.Integration.LocalComparisonFunctionalReclosure
import YM.Integration.LocalComparisonFullDensity
import YM.Integration.LocalComparisonPreReset
import YM.Integration.LocalComparisonPreResetDensity
import YM.Integration.NativeWeakIncomingReserve
import YM.Integration.RunFormalChain
import YM.Trace.Physicalv2.Germ
import YM.Comparison.RG02.Symmetry.Code

/-!
# A global, same-polynomial candidate for the literal local comparison

The local comparison fixes the setup and its rendering as hypotheses.
This file states global conclusions and proves conditional implications
for their consumers. The weaker intake supplies a same-scale support/tree
reserve. Application to the full native strong output also requires the
fine-to-coarse integrated seed reserve, an analytic supplier and admission
of the actual Run. `UniformContract` describes the candidate uniform
contract. `StrongContract` states the fixed contract for the strong input.

UniformContract fixes the finite setup and widths, then C_J and a polynomial
degree, before the physical Family and full Bulk.Chain. Concrete admission,
the permitted post-block constants, and finite hull multipliers follow that
choice. The original local datum must satisfy their concrete short-hull
injectivity conditions. For each fixed
positive delta and requested forced power, a single stage threshold precedes
every cutoff, period, datum, representation layout, and independent unit test.
The representation is selected before every such request. All its conclusions
refer to the SAME represented output of the SAME full unnormalized polynomial.

No next-use price, calibration solution, reset, or repeated-use admission is
an external conclusion here. A separately proved next-use budget is required
by `Result.with_next_price`. The unmasked whole-action correspondence is an
explicit antecedent, not a new conclusion or a freely chosen scalar family.

Locality below is tested on complete independent-test/field functionals.
Identically zero padded rows retain their original tags and supports. The
functional next-price path needs no unconditional zero-row locality; the old
stronger interface is available through `Result.with_next_price_strong`.
Application to the original construction still requires the width schedule,
its attachment to that construction, the analytic preparation and the
integrated seed reserve.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.Global

open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}

/-- All finite choices made before admission and before the actual-tail
threshold. Distinct slots retain their own complete test spaces. -/
structure Setup (V : Type) where
  order : ℕ
  order_ge_two : 2 ≤ order
  eta : ℝ
  eta_pos : 0 < eta
  eta_lt_half : eta < 1 / 2
  inputHorizon : ℕ
  outputHorizon : ℕ
  inputWeight : V → ℕ
  outputWeight : V → ℕ
  input_weight_le v : inputWeight v ≤ inputHorizon
  output_weight_le v : outputWeight v ≤ outputHorizon
  inputFieldOrder : ℕ
  outputFieldOrder : ℕ
  field_minimum : 6 ≤ outputFieldOrder
  inputDistanceOrder : ℕ
  outputDistanceOrder : ℕ
  distance_minimum : 2 ≤ outputDistanceOrder
  field_reserve : outputFieldOrder ≤ inputFieldOrder
  distance_reserve : outputDistanceOrder ≤ inputDistanceOrder
  input_engineering : inputHorizon ≤ inputFieldOrder
  output_engineering : outputHorizon ≤ outputFieldOrder
  inputWidth : ℕ → ℝ
  outputWidth : ℕ → ℝ
  input_width_pos m : 0 < inputWidth m
  output_width_pos m : 0 < outputWidth m
  width_reserve m : outputWidth m < inputWidth m
  spareSupport : ℝ
  spare_support_positive : 0 < spareSupport
  reserveFugacity : ℝ
  reserve_fugacity_nonnegative : 0 ≤ reserveFugacity
  reserve_fugacity_lt_one : reserveFugacity < 1
  inputSupport : ℝ
  outputSupport : ℝ
  output_support_pos : 0 < outputSupport
  support_reserve : outputSupport < inputSupport
  tests : V → ComparisonDensity.Address.Orbit
  test_order v : max (inputWeight v) (outputWeight v) + 2 ≤ (tests v).D
  inheritedConstant : ℝ
  inherited_constant_nonnegative : 0 ≤ inheritedConstant
  physicalPeriodLower : ℝ
  physical_period_nonnegative : 0 ≤ physicalPeriodLower
  vacuumRankCap : ℕ
  inputPacketRankCap : ℕ
  outputPacketRankCap : ℕ
  inputPacketPowerCap : ℕ
  outputPacketPowerCap : ℕ
  forcedConstant : ℝ
  forced_constant_nonnegative : 0 ≤ forcedConstant

/-- One preselected family of derivative/support norms and analytic widths.
The width and post-block-cost schedules precede every concrete local input.
This record makes no assertion that the retained construction has purchased
these requirements; that is an application obligation. -/
structure Admission (C : Family G) (J : Setup V) where
  inputNorm : ℕ → BudgetPoint
  outputNorm : ℕ → BudgetPoint
  input_norm m : NormAt C (m + 1) (inputNorm m)
    J.inputFieldOrder J.inputDistanceOrder J.inputSupport
  output_norm m : NormAt C m (outputNorm m)
    J.outputFieldOrder J.outputDistanceOrder J.outputSupport
  inputWidth : ℕ → ℝ
  outputWidth : ℕ → ℝ
  input_width_pos m : 0 < inputWidth m
  output_width_pos m : 0 < outputWidth m
  width_reserve m : outputWidth m < inputWidth m
  input_width_eq : inputWidth = J.inputWidth
  output_width_eq : outputWidth = J.outputWidth
  admittedCost : ℕ → ℝ
  admitted_cost_nonnegative m : 0 ≤ admittedCost m
  admitted_cost_ge_one m : 1 ≤ admittedCost m
  radiusLoss : ℕ → ℝ
  radius_loss_positive m : 0 < radiusLoss m
  radius_loss_ge_one m : 1 ≤ radiusLoss m
  calibrationCap : ℕ → ℝ
  calibration_cap_nonnegative m : 0 ≤ calibrationCap m
  calibration_cap_tendsto : Tendsto calibrationCap atTop (𝓝 0)
  cost_covers_widths m : (inputWidth m)⁻¹ + (outputWidth m)⁻¹ +
    radiusLoss m ≤ admittedCost m
  cost_covers_geometry m :
    1 + (C.path.levels.clock.coverSize m : ℝ) +
      (C.path.levels.clock.coverSize (m + 1) : ℝ) +
      C.path.levels.clock.monitor m + C.path.levels.clock.monitor (m + 1) +
      C.path.levels.clock.loopCap m + C.path.levels.clock.loopCap (m + 1) +
      (C.path.levels.params m).paths + (C.path.levels.params (m + 1)).paths +
      (C.path.levels.params m).columns + (C.path.levels.params (m + 1)).columns +
      (C.path.levels.params m).clip.relaxation +
      (C.path.levels.params (m + 1)).clip.relaxation ≤ admittedCost m
  cost_covers_units m N period (hm : m < N) :
    C.path.levels.clock.threshold m /
        Pert.Asymptotics.regulatorRun C N period (m + 1) +
      C.path.levels.clock.threshold (m + 1) /
        Pert.Asymptotics.regulatorRun C N period (m + 1) ≤ admittedCost m
  cost_subpower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ start : ℕ, ∀ m : ℕ, start ≤ m → ∀ N period : ℕ, m < N →
      admittedCost m ≤ Pert.Asymptotics.regulatorRun C N period (m + 1) ^ (-epsilon)
  pathRate : ℕ → ℝ
  path_rate_positive m : 0 < pathRate m
  path_rate_width m : pathRate m ≤ min (inputWidth m) (outputWidth m)
  path_rate_cost m : (pathRate m)⁻¹ ≤ admittedCost m
  regular_flat (costPower couplingPower targetPower : ℕ) :
    ∃ start : ℕ, ∀ m : ℕ, start ≤ m → ∀ N period : ℕ, m < N →
      admittedCost m ^ costPower *
        (Pert.Asymptotics.regulatorRun C N period (m + 1)) ^ (-(couplingPower : ℝ)) *
        Real.exp (-pathRate m * (C.path.levels.clock.coverSize m : ℝ)) ≤
      (Pert.Asymptotics.regulatorRun C N period (m + 1)) ^ targetPower
  forced_flat (delta : ℝ) (hdelta : 0 < delta)
      (costPower couplingPower denominatorPower targetPower : ℕ) :
    ∃ start : ℕ, ∀ m : ℕ, start ≤ m → ∀ N period : ℕ, m < N →
      admittedCost m ^ costPower *
        (Pert.Asymptotics.regulatorRun C N period (m + 1)) ^ (-(couplingPower : ℝ)) *
        Real.exp (-pathRate m * (C.path.levels.clock.monitor m) ^ delta /
          (1 + (C.path.levels.clock.coverSize m : ℝ)) ^ denominatorPower) ≤
      (Pert.Asymptotics.regulatorRun C N period (m + 1)) ^ targetPower

variable {J : Setup V}

/-- A local representation on the fixed physical lattice and operator.
Its density is deliberately NOT identified with the selected trajectory.
That additional equality belongs to the actual-Run specialization. -/
structure StepCarrier (C : Family G) (N period level : ℕ) where
  rep : Rep G (C.side level period)
  path : rep.path = (C.path.rep N period level).path
  clip : rep.clip = (C.path.rep N period level).clip
  point : rep.p = C.path.levels.budget level

/-- The old trajectory carrier is recovered only with the actual density
identity; none is inferred from having the same stencil and norm. -/
def StepCarrier.onActual {N period level : ℕ}
    (Q : StepCarrier C N period level)
    (h : Q.rep.eval = (C.path.rep N period level).eval) :
    Carrier C N period level :=
  ⟨Q.rep, Q.path, Q.clip, Q.point, h⟩

/-- Minimal analytic structure, without the value/affine-null requirements
of `Activities.Valid`. Non-affine calibration and the pre-reset kinetic
receipt therefore remain admissible. Every original row is summable. -/
structure WellFormed {n : Side} (p : BudgetPoint) (P : Rep G n) where
  threshold : p.threshold = P.p.threshold
  regular i : p.Regular (P.activities.reg i).support (P.activities.E i)
  regular_sum U : Summable (fun i => P.activities.regularOccurrence P.p i U)
  regularCost : ℝ
  regular_cost_nonnegative : 0 ≤ regularCost
  regular_bound : P.activities.EBound p regularCost
  forced : P.activities.ForcedFamily P.p
  moves s b : Nonempty (P.activities.Moves s b)

/-- The complete preparation on a general local vacuum. Its actual-Run
specialization below is definitionally the existing prepared input. -/
structure Prepared {D : V → ComparisonDensity.Address.Orbit}
    (N period level : ℕ) (Q : StepCarrier C N period level)
    (roots : V → Site (C.side level period))
    (input : Taste (TestSpace D) roots Q.rep R)
    (colors : TestSpace D → Bulk.Colors R G (C.side level period))
    (packets : MarkedPackets D G (C.side level period) R)
    (w : V → ℝ) (kernelEnvelope : R.Mode → ℝ) (forcedPrice : ℝ) where
  convention : InputColors colors packets
  remainder : Taste (TestSpace D) roots Q.rep R
  regular_zero x i : remainder.menu.regular x i = 0
  unit_zero x v : remainder.menu.global x v = 0
  caption_zero x i : remainder.score x i = 0
  full (x : TestSpace D) (U : Config G (C.side level period)) :
    (input.leaf x).density U =
      Poly.pass (packets.read x (Pert.Asymptotics.regulatorRun C N period level) U) *
        (remainder.leaf x).density U
  forced_price : RelativeBudget (C.path.levels.budget level)
    (pullback (testInclusion D) remainder) w (forcedDivisor C level)
    kernelEnvelope 0 forcedPrice

/-- The same actual operator, before normalization, for both the scalar
vacuum and the complete marked polynomial. The scalar equation has not
silently replaced its input by the fixed trajectory vacuum. -/
structure Transition {N period level : ℕ} {X : Type*}
    (Q : StepCarrier C N period (level + 1))
    (Q' : StepCarrier C N period level)
    (o : V → Site (C.side (level + 1) period))
    (o' : V → Site (C.side level period))
    (input : Taste X o Q.rep R) (output : Taste X o' Q'.rep R) : Prop where
  roots v : (C.path.levels.clock.op level period).ratio.parent (o v) = o' v
  vacuum : (C.path.levels.clock.op level period).push
    (C.path.β N period (level + 1)) Q.rep.eval = Q'.rep.eval
  density x : actualPush C N period level ((input.leaf x).density) =
    (output.leaf x).density

/-- The original coarse denominator follows from the full scalar push and
an original fine denominator. No second vacuum is selected. -/
theorem Transition.actual_output {N period level : ℕ} {X : Type*}
    {Q : StepCarrier C N period (level + 1)} {Q' : StepCarrier C N period level}
    {o : V → Site (C.side (level + 1) period)}
    {o' : V → Site (C.side level period)}
    {input : Taste X o Q.rep R} {output : Taste X o' Q'.rep R}
    (T : Transition Q Q' o o' input output) (hC : C.Makes) (hlevel : level < N)
    (hInput : Q.rep.eval = (C.path.rep N period (level + 1)).eval) :
    Q'.rep.eval = (C.path.rep N period level).eval := by
  calc
    Q'.rep.eval = (C.path.levels.clock.op level period).push
        (C.path.β N period (level + 1)) Q.rep.eval := T.vacuum.symm
    _ = (C.path.levels.clock.op level period).push
        (C.path.β N period (level + 1))
        (C.path.rep N period (level + 1)).eval := congrArg _ hInput
    _ = (C.path.rep N period level).eval :=
      (hC.wilson.steps N period level hlevel).1.symm

/-- Global constants and schedules. No field can depend on the cutoff,
period, datum, chosen tests, or output representation. The polynomial and
subpower witnesses are shared as well. -/
structure Prices (A : Admission C J) where
  vacuumConstant : ℝ
  vacuum_constant_nonnegative : 0 ≤ vacuumConstant
  markedConstant : ℝ → ℝ
  marked_constant_nonnegative delta : 0 < delta → 0 ≤ markedConstant delta
  vanishing : ℕ → ℝ
  vanishing_nonnegative m : 0 ≤ vanishing m
  vanishing_tendsto : Tendsto vanishing atTop (𝓝 0)
  geometry : ℕ → ℝ
  geometry_nonnegative m : 0 ≤ geometry m
  polynomialConstant : ℝ
  polynomial_constant_nonnegative : 0 ≤ polynomialConstant
  polynomialDegree : ℕ
  polynomial_bound m : geometry m ≤
    polynomialConstant * (1 + A.admittedCost m) ^ polynomialDegree
  hullMultiplier : ℕ → ℕ
  hull_positive m : 0 < hullMultiplier m
  hull_bound m : (hullMultiplier m : ℝ) ≤
    polynomialConstant * (1 + A.admittedCost m) ^ polynomialDegree
  subpower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ start : ℕ, ∀ m : ℕ, start ≤ m → ∀ N period : ℕ, m < N →
      geometry m ≤
        Pert.Asymptotics.regulatorRun C N period (m + 1) ^ (-epsilon)

/-- Concrete finite short-hull admission. The post-block multiplier is chosen
with the common price witnesses before any datum or test, and is covered by
the same fixed-degree geometric envelope. Every translated cover box is
required to inject into the original torus. The analytic construction owes
containment of its finitely enlarged hulls in these boxes; no all-power room
condition or arbitrary admission predicate is used. -/
structure ShortHulls {J : Setup V} {A : Admission C J} (K : Prices A)
    (datum : LocalFormal.Datum C R) : Prop where
  coarse (o : Site (C.side datum.level datum.period)) :
    Set.InjOn (fun z : Cover => o + wrap (C.side datum.level datum.period) z)
      (↑(box (K.hullMultiplier datum.level *
        (1 + C.path.levels.clock.coverSize datum.level))) : Set Cover)
  fine (o : Site (C.side (datum.level + 1) datum.period)) :
    Set.InjOn (fun z : Cover => o + wrap (C.side (datum.level + 1) datum.period) z)
      (↑(box (K.hullMultiplier datum.level *
        (1 + C.path.levels.clock.coverSize (datum.level + 1)))) : Set Cover)

private theorem translated_box_injective (n : Side) (r : ℕ)
    (hsize : 2 * r < n.val) (o : Site n) :
    Set.InjOn (fun z : Cover => o + wrap n z) (↑(box r) : Set Cover) := by
  have hsize' : (2 : ℤ) * r < n.val := by exact_mod_cast hsize
  have centered (z : Cover) (hz : z ∈ box r) :
      ∀ i, -(n.val : ℤ) < 2 * z i ∧ 2 * z i ≤ n.val := by
    obtain ⟨hl, hu⟩ := box_test.mp hz
    intro i
    have hlo := hl i
    have hup := hu i
    omega
  intro x hx y hy hxy
  exact wrap_injOn n (centered x hx) (centered y hy) (add_left_cancel hxy)

omit [Fintype V] in
/-- A concrete numerical inlet for the finite hull receipt. It preserves the
original torus at each side and uses only the actual selected multiplier. -/
theorem ShortHulls.of_size {J : Setup V} {A : Admission C J} (K : Prices A)
    (datum : LocalFormal.Datum C R)
    (coarse : 2 * (K.hullMultiplier datum.level *
      (1 + C.path.levels.clock.coverSize datum.level)) <
        (C.side datum.level datum.period).val)
    (fine : 2 * (K.hullMultiplier datum.level *
      (1 + C.path.levels.clock.coverSize (datum.level + 1))) <
        (C.side (datum.level + 1) datum.period).val) : ShortHulls K datum where
  coarse o := translated_box_injective _ _ coarse o
  fine o := translated_box_injective _ _ fine o

/-- The original packet functions with masks removed, retaining every
original summand. This definition introduces no new analytic completion. -/
def unmaskedPayload {n : Side} (P : Payload G n) (U : Config G n) : ℝ :=
  ∑' i : ℕ, P.action i U

def unmaskedLayers {n : Side} (layers : List (Piece G n))
    (g : ℝ) (U : Config G n) : ℝ :=
  (layers.map fun a => Render.prefactor g a * unmaskedPayload a.packet U).sum

/-- Literal invariant curvature atoms for the supplied vacuum layers.
Every original payload row, root, and support is retained. The common
coefficient sums carry the TRUE exponential path lengths before rendering;
smoothness or finite formal-jet agreement alone does not supply this record.
-/
structure VacuumPackets {n : Side} (layers : List (Piece G n))
    (p : BudgetPoint) (rankCap : ℕ) (width budget : ℝ) where
  atom : (a : Piece G n) → ℕ → Atom G a.rank
  rank_bounded a : a ∈ layers → a.rank ≤ rankCap
  invariant a : a ∈ layers → ∀ i, (atom a i).Invariant
  original_action a : a ∈ layers → ∀ i U,
    a.packet.action i U = (atom a i).unmasked U (a.packet.labels i).site
  support a : a ∈ layers → ∀ i,
    (atom a i).footprint (a.packet.labels i).site ⊆ (a.packet.labels i).support
  pieceCost : Piece G n → ℝ
  piece_cost_nonnegative a : a ∈ layers → 0 ≤ pieceCost a
  exponential a : a ∈ layers → ∀ o,
    RG.SumBudget
      (fun i : ℕ => if (a.packet.labels i).site = o then
        (atom a i).magnitude * Real.exp (width * (atom a i).length) else 0)
      (pieceCost a)
  total : (layers.map pieceCost).sum ≤ budget
  coverOffset : ℕ
  coverSlope : ℕ
  cover a : a ∈ layers → ∀ i,
    p.B * (coverNumber p.B (a.packet.labels i).support : ℝ) ≤
      coverOffset * p.B + coverSlope * (atom a i).length
  width_reserved : p.supportExponent * coverSlope / p.B ≤ width / 4
  cover_cost : Real.exp (p.supportExponent * coverOffset) ≤ budget

/-- The complete prescribed output action: the retained path action (base,
cubic, quartic, and loop), the prescribed kinetic increment, and ALL extra
packets. Its value at zero coupling is supplied only by a genuine smooth
extension in `WholeAction`; it is never declared to be its arbitrary value
under division by zero. -/
def modelAction {N period order : ℕ} (P : Plan C N period order)
    (m : ℕ) (g : ℝ) (U : Config G (C.side m period)) : ℝ :=
  (C.path.rep N period m).path.inChannels
      (C.path.levels.params m).clip (C.path.levels.budget m)
      ((g ^ 2)⁻¹ + P.poly m g) U +
    unmaskedLayers (P.layers m) (Currency.gain ((g ^ 2)⁻¹ + P.poly m g)) U

/-- Application-side identification with the WHOLE formal vacuum action.
The input equality compares the two COMPLETE native action expressions.
In particular it does not guess an extra-packet-only coefficient identity.
The output coefficient identity includes `Orbit.ground`'s leading base price,
not only `logVac`; an arbitrary field-independent scalar may be extracted.

Producing this record from a retained Run/Plan is a separate mathematical
obligation. Merely having a `Coin`, or matching marked coefficients alone,
does not produce it. -/
structure WholeAction (Y : Bulk.Chain C.path) (J : Setup V)
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

/-- A possible non-affine calibration interaction. Both its regular norm
and its full-group coefficient sizes are charged at the stated price.
No value-nullness or affine-Hessian-nullness is imposed. The explicit
`Nat` layout and support sums precede all fields. -/
structure Calibration {n : Side} (p : BudgetPoint) (price : ℝ) where
  labels : ℕ → RegularAddress n
  action : ℕ → Config G n → ℝ
  regularMajorant : ℕ → ℝ
  fullMajorant : ℕ → ℝ
  regular i : p.Regular (labels i).support (action i)
  regular_bound i : p.supBounds (labels i).site (labels i).support
    (action i) (regularMajorant i)
  full_nonnegative i : 0 ≤ fullMajorant i
  full_bound i U : |action i U| ≤ fullMajorant i
  regular_total o : RG.SumBudget
    (fun i => if (labels i).site = o then
      p.mass (labels i).support (regularMajorant i) else 0) price
  full_total o : RG.SumBudget
    (fun i => if (labels i).site = o then
      p.mass (labels i).support (fullMajorant i) else 0) price

def Calibration.amount {n : Side} {p : BudgetPoint} {price : ℝ}
    (E : Calibration (G := G) (n := n) p price) (U : Config G n) : ℝ :=
  ∑' i : ℕ, masked p.threshold (E.labels i).support (E.action i) U

/-- Exact vacuum input decomposition on the original carrier. The nonlinear
gas is not logarithmically inserted into a fictitious analytic action; all
its original forced rows remain those of `Q.rep`.

The inherited `error` is in the value/affine-null Wilson class, whereas the
calibration is separately bounded and may be non-affine. This is an input
receipt, not a construction of calibration or a same-Run Plan accessor.
-/
structure VacuumInput (J : Setup V) (A : Admission C J)
    (datum : LocalFormal.Datum C R)
    (P : Plan C datum.cutoff datum.period J.order)
    (Q : StepCarrier C datum.cutoff datum.period (datum.level + 1))
    (inherited calibration : ℝ) where
  error : Payload G (C.side (datum.level + 1) datum.period)
  error_paid : error.Invoice (A.inputNorm datum.level) inherited
  extra : Calibration (G := G) (n := C.side (datum.level + 1) datum.period)
    (A.inputNorm datum.level) calibration
  layers_paid : Render.permits (P.layers (datum.level + 1)) (A.inputNorm datum.level)
  output_layers_paid : Render.permits (P.layers datum.level) (A.outputNorm datum.level)
  analytic_input : VacuumPackets (P.layers (datum.level + 1))
    (A.inputNorm datum.level) J.vacuumRankCap
    (A.inputWidth datum.level) (A.admittedCost datum.level)
  analytic_output : VacuumPackets (P.layers datum.level)
    (A.outputNorm datum.level) J.vacuumRankCap
    (A.outputWidth datum.level) (A.admittedCost datum.level)
  structure_valid : WellFormed (A.inputNorm datum.level) Q.rep
  exponent (U : Config G (C.side (datum.level + 1) datum.period)) :
    Q.rep.exponent U = Q.rep.scalar -
      ((C.path.rep datum.cutoff datum.period (datum.level + 1)).path.inChannels
        Q.rep.clip Q.rep.p (C.path.β datum.cutoff datum.period (datum.level + 1)) U +
        Render.renders
          (Render.prefactor
            (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
          Q.rep.p U (P.layers (datum.level + 1))) -
      error.amount (A.inputNorm datum.level) U - extra.amount U

/-- One concrete admissible input. All packet layouts, root addresses,
radii, and envelopes are selected before the independent tests. `Paid`
contains actual exponential path/connector and derivative-support reserves.
The explicit vacuum decomposition retains every original K and separately
charges a possible non-affine calibration term.
-/
structure Input (Y : Bulk.Chain C.path) (J : Setup V)
    (A : Admission C J) (datum : LocalFormal.Datum C R) where
  plan : Plan C datum.cutoff datum.period J.order
  inherited : ℝ
  calibration : ℝ
  inherited_nonnegative : 0 ≤ inherited
  calibration_nonnegative : 0 ≤ calibration
  calibration_bound : calibration ≤ A.calibrationCap datum.level
  inherited_bound : inherited ≤ J.inheritedConstant *
    Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1) ^
      ((J.order : ℝ) + 1 - J.eta)
  inputCarrier : StepCarrier C datum.cutoff datum.period (datum.level + 1)
  vacuum_input : VacuumInput J A datum plan inputCarrier inherited calibration
  physical_period : J.physicalPeriodLower ≤ (C.S.period datum.period).val
  input_field_admitted : J.inputFieldOrder ≤
    (C.path.levels.budget (datum.level + 1)).order
  input_distance_admitted : J.inputDistanceOrder ≤
    (C.path.levels.budget (datum.level + 1)).power
  output_field_admitted : J.outputFieldOrder ≤ (C.path.levels.budget datum.level).order
  output_distance_admitted : J.outputDistanceOrder ≤ (C.path.levels.budget datum.level).power
  fineRoots : V → Site (C.side (datum.level + 1) datum.period)
  coarseRoots : V → Site (C.side datum.level datum.period)
  roots v : (C.path.levels.clock.op datum.level datum.period).ratio.parent (fineRoots v) =
    coarseRoots v
  input : Taste (TestSpace J.tests) fineRoots inputCarrier.rep R
  input_multilinear : Multilinear J.tests input
  colors : TestSpace J.tests → Bulk.Colors R G
    (C.side (datum.level + 1) datum.period)
  inputPackets : MarkedPackets J.tests G (C.side (datum.level + 1) datum.period) R
  input_rank_bounded : inputPackets.rankCap ≤ J.inputPacketRankCap
  input_power_bounded : inputPackets.powerCap ≤ J.inputPacketPowerCap
  inputRadii : V → ℝ
  inputKernelCosts : V → ℝ
  inputForcedPrice : ℝ
  input_forced_bound : inputForcedPrice ≤ J.forcedConstant
  prepared : Prepared datum.cutoff datum.period (datum.level + 1)
    inputCarrier fineRoots input colors inputPackets inputRadii
    (envelopeProduct inputKernelCosts) inputForcedPrice
  input_kernel_positive v : 0 < inputKernelCosts v
  model : MarkedPackets J.tests G (C.side datum.level datum.period) R
  output_rank_bounded : model.rankCap ≤ J.outputPacketRankCap
  output_power_bounded : model.powerCap ≤ J.outputPacketPowerCap
  prescribed : PrescribedPackets Y datum colors model J.order
  whole_action : WholeAction Y J datum colors plan
  outputRadii : V → ℝ
  outputKernelCosts : V → ℝ
  output_kernel_positive v : 0 < outputKernelCosts v
  kernel_envelopes v : inputKernelCosts v ≤ outputKernelCosts v
  radius_admission v : outputRadii v * A.radiusLoss datum.level ≤ inputRadii v
  inputAddresses : V → Support (C.side (datum.level + 1) datum.period)
  outputAddresses : V → Support (C.side datum.level datum.period)
  output_address_transport v : outputAddresses v =
    (inputAddresses v).image
      (C.path.levels.clock.op datum.level datum.period).ratio.parent
  output_origins v : coarseRoots v ∈ outputAddresses v
  input_retains : FunctionalRetains input inputAddresses
  inputRegion : Comparison.Density.Testing.Region
    (fun v => (J.tests v).Mood) (C.side (datum.level + 1) datum.period)
  outputRegion : Comparison.Density.Testing.Region
    (fun v => (J.tests v).Mood) (C.side datum.level datum.period)
  inputCoverOffset : ℕ
  inputCoverSlope : ℕ
  outputCoverOffset : ℕ
  outputCoverSlope : ℕ
  input_cover_cost : Real.exp
    ((A.inputNorm datum.level).supportExponent * inputCoverOffset) ≤
      A.admittedCost datum.level
  output_cover_cost : Real.exp
    ((A.outputNorm datum.level).supportExponent * outputCoverOffset) ≤
      A.admittedCost datum.level
  input_paid : inputPackets.Paid (A.inputNorm datum.level) inputAddresses
    inputRegion (fun v => inputRadii v / inputKernelCosts v)
    (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
    (A.inputWidth datum.level) (A.admittedCost datum.level)
    inputCoverOffset inputCoverSlope
  output_paid : model.Paid (A.outputNorm datum.level) outputAddresses outputRegion
    (fun v => outputRadii v / outputKernelCosts v)
    (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
    (A.outputWidth datum.level) (A.admittedCost datum.level)
    outputCoverOffset outputCoverSlope
  primary_admitted v : C.ref (J.outputWeight v) ≤ datum.level

/-- Positivity is already paid by the literal packet norm. -/
theorem Input.inputRadii_pos {Y : Bulk.Chain C.path} {J : Setup V}
    {A : Admission C J} {datum : LocalFormal.Datum C R}
    (I : Input Y J A datum) (v : V) : 0 < I.inputRadii v :=
  (div_pos_iff_of_pos_right (I.input_kernel_positive v)).mp (I.input_paid.positive v)

/-- The primary prefactor therefore cannot vanish through a zero radius. -/
theorem Input.outputRadii_pos {Y : Bulk.Chain C.path} {J : Setup V}
    {A : Admission C J} {datum : LocalFormal.Datum C R}
    (I : Input Y J A datum) (v : V) : 0 < I.outputRadii v :=
  (div_pos_iff_of_pos_right (I.output_kernel_positive v)).mp (I.output_paid.positive v)

/-- The original strong incoming vacuum estimates, at both the actual
norm and the reserved fixed norm. -/
structure StrongIntake {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {datum : LocalFormal.Datum C R} (I : Input Y J A datum) : Prop where
  original : I.inputCarrier.rep.activities.KBound
    (C.path.levels.budget (datum.level + 1))
    (C.path.levels.clock.forcedAllowance (datum.level + 1))
  reserved : I.inputCarrier.rep.activities.KBound (A.inputNorm datum.level)
    (C.path.levels.clock.forcedAllowance (datum.level + 1))

/-- The strong alternative and a proposed weaker incoming K domain. The weaker alternative uses
original support norms and the actual normalized marked predivision masses,
with one unit for the native tree and the fixed spare support for subsequent
attachments. Only half of the scalar tree budget is spent. The actual future
attachment mass and its support loss must be bounded in the construction;
no future mask-change family or output estimate is assumed. -/
inductive Intake {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {datum : LocalFormal.Datum C R} (I : Input Y J A datum) where
  | strong (bound : StrongIntake I)
  | weak (w0 : ℝ)
      (bound : WeakReserve (A.inputNorm datum.level)
        (priceNormalized (envelopeProduct I.inputKernelCosts)
          (pullback (testInclusion J.tests) I.prepared.remainder))
        I.inputRadii (forcedDivisor C (datum.level + 1)) 0 I.inputForcedPrice
        (J.outputSupport + J.spareSupport) w0 J.reserveFugacity)
      (margin : ((A.inputNorm datum.level).B + (A.inputNorm datum.level).B + 1 : ℕ)^4 *
        (w0 ^ (1 - J.reserveFugacity) + (Fintype.card V : ℝ) *
          (forcedDivisor C (datum.level + 1) * I.inputForcedPrice)) ≤ 1 / 2)

/-- The common represented output before imposing any prices. -/
structure Output {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {datum : LocalFormal.Datum C R} (I : Input Y J A datum) where
  carrier : StepCarrier C datum.cutoff datum.period datum.level
  structure_valid : WellFormed (A.outputNorm datum.level) carrier.rep
  actual_forced : carrier.rep.activities.KBound (C.path.levels.budget datum.level)
    (C.path.levels.clock.forcedAllowance datum.level)
  output : Taste (TestSpace J.tests) I.coarseRoots carrier.rep R
  output_active (x : TestSpace J.tests) : (output.leaf x).Active
  residual : Taste (TestSpace J.tests) I.coarseRoots carrier.rep R
  exact : Transition I.inputCarrier carrier I.fineRoots I.coarseRoots I.input output
  output_multilinear : Multilinear J.tests output
  residual_multilinear : Multilinear J.tests residual
  output_retains : FunctionalRetains output I.outputAddresses
  residual_retains : FunctionalRetains residual I.outputAddresses
  full (x : TestSpace J.tests) (U : Config G (C.side datum.level datum.period)) :
    (output.leaf x).density U =
      Poly.pass (I.model.read x
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) U) *
      (residual.leaf x).density U
  vacuum_reserve : carrier.rep.activities.KBound (A.outputNorm datum.level)
    (C.path.levels.clock.forcedAllowance datum.level)

/-- Forced-only part of the complete represented norm. Its single original
`Nat x Nat` majorant is chosen before all tests AND every group field.
It makes no regular-output or next-use assertion. -/
structure ForcedBudget {n : Side} {P : Rep G n} {X : Type*}
    {o : V → Site n} (p : BudgetPoint) (T : Taste X o P R)
    (w : V → ℝ) (divisor price : ℝ) where
  black : ℕ × ℕ → ℝ
  black_nonnegative i : 0 ≤ black i
  forced (x : X) (i j : ℕ) (U : Config G n) :
    ‖T.menu.force x i j U‖ ≤ black (i, j)
  total (v : V) : RG.SumBudget
    (fun i : ℕ × ℕ => if v ∈ (T.menu.marks i.1 i.2).val then
      Poly.toll w (T.menu.marks i.1 i.2) *
        p.mass (P.activities.forced i.1).support (black i) else 0)
    (divisor * price)

/-- Exact native primary extraction, tied to a singleton of this output.
The formal side uses the same output threshold, frame, roots, and literal
unmasked model. No arbitrary linear observer is substituted for pi-natural.
-/
structure PrimaryData {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {datum : LocalFormal.Datum C R} {I : Input Y J A datum}
    (O : Output I) where
  coefficient : (v : V) → TestSpace J.tests →
    Source.Coefficient (C.labels.level (J.outputWeight v))
      (C.side datum.level datum.period)
  support v x y : (coefficient v x).support = (coefficient v y).support
  format v x : (coefficient v x).Format (I.coarseRoots v) C.params O.carrier.rep
  remainder v x : ∃ k r, (coefficient v x).remBound (I.coarseRoots v) O.carrier.rep k r
  singleton v x U :
    (coefficient v x).density (I.coarseRoots v)
        (C.localSection (J.outputWeight v)) O.carrier.rep U =
      ((O.output.leaf x).density U).part (R.fire v)

/-- A price on the already selected primary coordinates. No new coefficient
or representation is chosen when the requested delta changes. -/
def PrimaryData.Bound {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {datum : LocalFormal.Datum C R} {I : Input Y J A datum} {O : Output I}
    (P : PrimaryData O) (price : ℝ) : Prop :=
    ∀ (v : V) (x : IndependentTests J.tests),
    (I.outputRadii v / I.outputKernelCosts v) *
      (C.labels.level (J.outputWeight v)).coeffSize
        (Trace.Physical.Germ.projection (C.labels.level (J.outputWeight v)) C.params
            O.carrier.rep.p.threshold (I.coarseRoots v)
            (P.coefficient v (testInclusion J.tests x)) -
          Trace.Physical.Germ.vector (C.labels.level (J.outputWeight v)) C.params
            O.carrier.rep.p.threshold (I.coarseRoots v)
            (fun U => (I.model.read (testInclusion J.tests x)
              (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
                (datum.level + 1)) U).part (R.fire v))) ≤ price

structure Primary {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {datum : LocalFormal.Datum C R} {I : Input Y J A datum}
    (O : Output I) (price : ℝ) extends PrimaryData O where
  bound : toPrimaryData.Bound price

/-- The pre-reset vacuum estimate on the SAME literal representation as
all marked conclusions. The fixed output norm remains distinct from the
larger stage-varying norm requested by a later native `Early` consumer.
The raw carrier retains every original hard row, the low/high alpha receipt,
and the entire prescribed model list; its evaluation identity is proved in
`LocalComparisonPreReset`, without performing the paid kinetic reset. -/
structure VacuumWitness {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    (K : Prices A) {datum : LocalFormal.Datum C R} (I : Input Y J A datum)
    (O : Output I) where
  listing : AnalyticBridge.VerifiedReset.Collection.Listing G
    (C.side datum.level datum.period)
  source : AnalyticBridge.VerifiedReset.Collection.Source G
    (C.side datum.level datum.period)
  scalar : ℝ
  estimate : AnalyticBridge.VerifiedReset.Collection.Local listing
    (A.outputNorm datum.level) source
    (vacuumRate J.order K.vacuumConstant (C.S.block datum.level).val
      (K.vanishing datum.level) (K.geometry datum.level) I.inherited I.calibration
      (Currency.g C datum.cutoff datum.period (datum.level + 1)))
    (C.path.levels.clock.forcedAllowance datum.level)
  representation : O.carrier.rep =
    PreReset.append (I.plan.layers datum.level)
      (C.path.rep datum.cutoff datum.period datum.level).path
      (C.path.levels.params datum.level).clip (C.path.levels.budget datum.level)
      listing source (I.plan.predict datum.level - I.plan.alpha datum.level)
      scalar (I.plan.alpha datum.level)
      (Render.prefactor (Currency.gain (I.plan.predict datum.level)))

/-- The local quote already proves the original raw summability. Only the
threshold equality is used to pass to the physical representation. -/
theorem VacuumWitness.source_summable {Y : Bulk.Chain C.path} {J : Setup V}
    {A : Admission C J} {K : Prices A} {datum : LocalFormal.Datum C R}
    {I : Input Y J A datum} {O : Output I} (W : VacuumWitness K I O)
    (U : Config G (C.side datum.level datum.period)) :
    Summable (fun i => (W.listing.read W.source).regularOccurrence
      (C.path.levels.budget datum.level) i U) := by
  have h := PreReset.series_of_EBound W.estimate.unweighted U
  simpa only [Activities.regularOccurrence, (A.output_norm datum.level).threshold] using h

/-- The literal output packet receipt proves summability of every model
layer at the physical mask threshold, without a new analytic assumption. -/
theorem VacuumWitness.model_summable {Y : Bulk.Chain C.path} {J : Setup V}
    {A : Admission C J} {K : Prices A} {datum : LocalFormal.Datum C R}
    {I : Input Y J A datum} {O : Output I} (W : VacuumWitness K I O)
    (a : Piece G (C.side datum.level datum.period)) (ha : a ∈ I.plan.layers datum.level)
    (U : Config G (C.side datum.level datum.period)) :
    Summable (fun i => masked (C.path.levels.budget datum.level).threshold
      (a.packet.labels i).support (a.packet.action i) U) := by
  have h := PreReset.payload_series (I.vacuum_input.output_layers_paid a ha)
    (W.listing.read W.source) U
  simpa only [(A.output_norm datum.level).threshold] using h

/-- The three literal qlocal conclusions on ONE output. `residual_price`
is the connected logarithmic price; disconnected coefficients are obtained
only through `Output.full` and the native exponential/product rule.
The additional forced price is on the full OUTPUT, not merely its residual.
-/
structure Result {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    (K : Prices A) {datum : LocalFormal.Datum C R} (I : Input Y J A datum)
    (delta : ℝ) (forcedOrder : ℕ) where
  output : Output I
  vacuum : VacuumWitness K I output
  residual_price : RelativeBudget (A.outputNorm datum.level)
    (pullback (testInclusion J.tests) output.residual) I.outputRadii
    (forcedDivisor C datum.level) (envelopeProduct I.outputKernelCosts)
    (markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited I.calibration
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
      forcedOrder)
  primary : Primary output
    (markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited I.calibration
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
  forced : ForcedBudget (A.outputNorm datum.level)
    (priceNormalized (envelopeProduct I.outputKernelCosts)
      (pullback (testInclusion J.tests) output.output)) I.outputRadii
    (forcedDivisor C datum.level)
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
      forcedOrder)

/-- The representation, its vacuum decomposition, and its actual primary
coordinates are selected once, before every delta and forced-power request. -/
structure SelectedOutput {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    (K : Prices A) {datum : LocalFormal.Datum C R} (I : Input Y J A datum) where
  output : Output I
  vacuum : VacuumWitness K I output
  primary : PrimaryData output

/-- Estimates on that one selected output. Only norm majorants and thresholds
may vary with the finite requested loss and power; the represented rows,
full polynomial and primary extraction remain fixed. -/
structure RequestBounds {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {K : Prices A} {datum : LocalFormal.Datum C R} {I : Input Y J A datum}
    (S : SelectedOutput K I) (delta : ℝ) (forcedOrder : ℕ) where
  residual_price : RelativeBudget (A.outputNorm datum.level)
    (pullback (testInclusion J.tests) S.output.residual) I.outputRadii
    (forcedDivisor C datum.level) (envelopeProduct I.outputKernelCosts)
    (markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited I.calibration
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
      forcedOrder)
  primary : S.primary.Bound
    (markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited I.calibration
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
  forced : ForcedBudget (A.outputNorm datum.level)
    (priceNormalized (envelopeProduct I.outputKernelCosts)
      (pullback (testInclusion J.tests) S.output.output)) I.outputRadii
    (forcedDivisor C datum.level)
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
      forcedOrder)

/-- Expose a finite requested result without changing any selected witness. -/
def SelectedOutput.result {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {K : Prices A} {datum : LocalFormal.Datum C R} {I : Input Y J A datum}
    {delta : ℝ} {forcedOrder : ℕ} (S : SelectedOutput K I)
    (H : RequestBounds S delta forcedOrder) : Result K I delta forcedOrder where
  output := S.output
  vacuum := S.vacuum
  residual_price := H.residual_price
  primary := { toPrimaryData := S.primary, bound := H.primary }
  forced := H.forced

/-- The finite-request bridge preserves the exact selected representation. -/
@[simp] theorem SelectedOutput.result_output
    {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {K : Prices A} {datum : LocalFormal.Datum C R} {I : Input Y J A datum}
    {delta : ℝ} {forcedOrder : ℕ} (S : SelectedOutput K I)
    (H : RequestBounds S delta forcedOrder) : (S.result H).output = S.output := rfl

/-- The primary extraction is equally unchanged by the requested bound. -/
@[simp] theorem SelectedOutput.result_primary
    {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {K : Prices A} {datum : LocalFormal.Datum C R} {I : Input Y J A datum}
    {delta : ℝ} {forcedOrder : ℕ} (S : SelectedOutput K I)
    (H : RequestBounds S delta forcedOrder) :
    (S.result H).primary.toPrimaryData = S.primary := rfl

/-- The required global output order: a single selector on an initial
admitted tail, then each delta/power with its own shared later threshold.
The weaker input-domain/seed-reserve identification remains open.
Nonempty intake is a proposition, so the selector does not depend on a choice
of proof or on a separately chosen weak-reserve witness. -/
structure FixedContract (Y : Bulk.Chain C.path) (J : Setup V)
    (admission : Admission C J) where
  prices : Prices admission
  start : ℕ
  select (datum : LocalFormal.Datum C R) (hm : start ≤ datum.level)
    (hulls : ShortHulls prices datum) (I : Input Y J admission datum) (hI : Nonempty (Intake I)) : SelectedOutput prices I
  bounds (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ later : ℕ, ∃ hlater : start ≤ later,
      ∀ (datum : LocalFormal.Datum C R) (hm : later ≤ datum.level)
        (hulls : ShortHulls prices datum)
        (I : Input Y J admission datum) (hI : Nonempty (Intake I)),
        Nonempty (RequestBounds
          (select datum (hlater.trans hm) hulls I hI) delta forcedOrder)

/-- A weaker, finite-request interface preserved for existing consumers.
The full contract constructs this by forgetting its common selector. -/
structure RequestFixedContract (Y : Bulk.Chain C.path) (J : Setup V)
    (admission : Admission C J) where
  prices : Prices admission
  compare (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ start : ℕ, ∀ datum : LocalFormal.Datum C R, start ≤ datum.level →
      ShortHulls prices datum → ∀ I : Input Y J admission datum, Intake I →
        Nonempty (Result prices I delta forcedOrder)

/-- Restrict to a finite request while retaining the original chosen output. -/
def FixedContract.requests {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    (H : FixedContract (R := R) Y J A) : RequestFixedContract (R := R) Y J A where
  prices := H.prices
  compare delta hdelta forcedOrder := by
    obtain ⟨later, hlater, hbound⟩ := H.bounds delta hdelta forcedOrder
    refine ⟨later, ?_⟩
    intro datum hm hulls I hI
    obtain ⟨B⟩ := hbound datum hm hulls I ⟨hI⟩
    exact ⟨(H.select datum (hlater.trans hm) hulls I ⟨hI⟩).result B⟩

/-- A finite-request strong-intake specialization. -/
structure StrongFixedContract (Y : Bulk.Chain C.path) (J : Setup V)
    (admission : Admission C J) where
  prices : Prices admission
  compare (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ start : ℕ, ∀ datum : LocalFormal.Datum C R, start ≤ datum.level →
      ShortHulls prices datum → ∀ I : Input Y J admission datum, StrongIntake I →
        Nonempty (Result prices I delta forcedOrder)

def FixedContract.strong {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    (H : FixedContract (R := R) Y J A) : StrongFixedContract (R := R) Y J A where
  prices := H.prices
  compare delta hdelta forcedOrder := by
    obtain ⟨start, hstart⟩ := H.requests.compare delta hdelta forcedOrder
    exact ⟨start, fun datum hm hulls I hI => hstart datum hm hulls I (Intake.strong hI)⟩

/-- Fixed-family form for one finite setup and its actual admission receipt.
This alone does not claim that C_J precedes the block schedule; that extra
uniformity is stated by UniformContract below. -/
def Contract (C : Family G) (Y : Bulk.Chain C.path) (J : Setup V)
    (admission : Admission C J) : Prop :=
  G.Simple → C.Makes → Nonempty (FixedContract (R := R) Y J admission)

def StrongContract (C : Family G) (Y : Bulk.Chain C.path) (J : Setup V)
    (admission : Admission C J) : Prop :=
  G.Simple → C.Makes → Nonempty (StrongFixedContract (R := R) Y J admission)

/-- The pre-block vacuum constant and fixed polynomial degree. Marked
constants and the numeric geometric prefactor retain the admitted post-block
dependence permitted by the manuscript. -/
structure PreBlockConstant where
  value : ℝ
  nonnegative : 0 ≤ value
  degree : ℕ

/-- Candidate uniform obligation over the displayed concrete domain.
Its weaker incoming alternative still needs the literal fine-to-coarse seed
reserve; this definition is not a proof or a complete identification of the
external supplier. The required strong output is not weakened.
The finite derivative/support choices and stage widths, then C_J and the
polynomial degree, precede
C and its block schedule. An Admission carries actual numerical delay
receipts, so no unconditional rule for inadmissible calendars is demanded.
C_delta, geometric costs, and their shared witnesses follow C/Admission and
still precede every datum, layout, and independent test. -/
def UniformContract : Prop :=
  G.Simple → ∀ (V : Type) [DecidableEq V] [Fintype V] (R : Census V) (J : Setup V),
    ∃ K : PreBlockConstant, ∀ (C : Family G) (Y : Bulk.Chain C.path), C.Makes →
      ∀ A : Admission C J,
        Nonempty { H : FixedContract (R := R) Y J A //
          H.prices.vacuumConstant = K.value ∧ H.prices.polynomialDegree = K.degree }

/-- Explicit same-Run specialization: both the physical family and the full
formal chain are taken from the original Run. -/
def ActualContract (run : PhysicalNext.Repeat.Legato.Run G) (J : Setup V)
    (admission : Admission run.family J) : Prop :=
  Contract (R := R) run.family (RunFormalChain.fromRun run) J admission

def StrongActualContract (run : PhysicalNext.Repeat.Legato.Run G) (J : Setup V)
    (admission : Admission run.family J) : Prop :=
  StrongContract (R := R) run.family (RunFormalChain.fromRun run) J admission

/-- Uniformity specializes to the original Run with its own admission receipt. -/
theorem UniformContract.atRun (H : UniformContract (G := G)) (hG : G.Simple)
    (run : PhysicalNext.Repeat.Legato.Run G) (J : Setup V)
    (A : Admission run.family J) :
    Nonempty (FixedContract (R := R) (RunFormalChain.fromRun run) J A) := by
  obtain ⟨K, hK⟩ := H hG V R J
  obtain ⟨F⟩ := hK run.family (RunFormalChain.fromRun run) run.makes A
  exact ⟨F.val⟩

/-- The threshold still precedes every concrete local datum and every test.
This reformulation only transports already shared witnesses. -/
theorem FixedContract.eventually_compare {Y : Bulk.Chain C.path}
    {J : Setup V} {A : Admission C J}
    (H : FixedContract (R := R) Y J A)
    (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ datum : LocalFormal.Datum C R,
      datum.level = m → ShortHulls H.prices datum →
        ∀ I : Input Y J A datum, Intake I →
        Nonempty (Result H.prices I delta forcedOrder) := by
  obtain ⟨start, hstart⟩ := H.requests.compare delta hdelta forcedOrder
  apply Filter.eventually_atTop.2
  refine ⟨start, ?_⟩
  intro m hm datum hlevel hulls I hI
  exact hstart datum (by simpa only [hlevel] using hm) hulls I hI

namespace Result

variable {Y : Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {K : Prices A} {datum : LocalFormal.Datum C R} {I : Input Y J A datum}
    {delta : ℝ} {forcedOrder : ℕ} (H : Result K I delta forcedOrder)

/-- The represented output is exactly the original full physical push. -/
theorem actual_density (x : TestSpace J.tests) :
    actualPush C datum.cutoff datum.period datum.level ((I.input.leaf x).density) =
      (H.output.output.leaf x).density :=
  H.output.exact.density x

/-- The formal factorization concerns the same full unnormalized polynomial,
including the actual unmarked denominator and every forced/mixed term. -/
theorem actual_factorization (x : TestSpace J.tests)
    (U : Config G (C.side datum.level datum.period)) :
    actualPush C datum.cutoff datum.period datum.level ((I.input.leaf x).density) U =
      Poly.pass (I.model.read x
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) U) *
        (H.output.residual.leaf x).density U := by
  rw [H.actual_density x]
  exact H.output.full x U

/-- A full regular/forced/mixed density consequence of the literal supplier.
It does not require a next-use budget. The remaining flagged exponential
background is retained explicitly, to be integrated by the actual-law
consumer; this is not a normalized integral estimate. -/
theorem residual_density_error_price
    (hSmall : C.path.levels.clock.forcedAllowance datum.level +
      (Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
          forcedOrder) ≤ 1)
    (x : IndependentTests J.tests) (U : Config G (C.side datum.level datum.period)) :
    let g := Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)
    let e := markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited I.calibration g
    Poly.price (fun v => I.outputRadii v / I.outputKernelCosts v)
      ((H.output.residual.leaf (testInclusion J.tests x)).density U -
        (H.output.carrier.rep.eval U : ℂ) • (1 : Poly R)) ≤
      |H.output.carrier.rep.eval U| * (Real.exp (Fintype.card V * e) - 1) +
      (Real.exp (H.output.carrier.rep.exponent U) * Real.exp (Fintype.card V * e)) *
        (if flags H.output.carrier.rep.p.threshold U = ∅ then 0 else
          ((Fintype.card V : ℝ) * (forcedDivisor C datum.level * g ^ forcedOrder)) *
            Real.exp (-SectorNext.Vacuum.flagRate (A.outputNorm datum.level) *
              (flags H.output.carrier.rep.p.threshold U).card)) := by
  exact PreResetDensity.full_density_error_price H.residual_price I.output_kernel_positive
    ((A.output_norm datum.level).threshold.trans
      (congrArg BudgetPoint.threshold H.output.carrier.point).symm)
    H.output.vacuum_reserve hSmall x U

/-- The output's exact pre-reset evaluation follows from the literal row
construction. This is an equality on every field, including failed masks. -/
theorem rendered_vacuum (hC : C.Makes)
    (U : Config G (C.side datum.level datum.period)) :
    H.output.carrier.rep.eval U =
      Reset.supplied (C.path.rep datum.cutoff datum.period datum.level).path
        (C.path.levels.params datum.level).clip (C.path.levels.budget datum.level)
        H.vacuum.listing H.vacuum.source
        (I.plan.predict datum.level - I.plan.alpha datum.level)
        H.vacuum.scalar (I.plan.alpha datum.level) U *
      Real.exp (-Render.renders (Render.prefactor (Currency.gain (I.plan.predict datum.level)))
        (C.path.levels.budget datum.level) U (I.plan.layers datum.level)) := by
  have hs := hC.wilson.represents datum.cutoff datum.period datum.level datum.below.le
  have hW : (C.path.rep datum.cutoff datum.period datum.level).path.Bounds
      (C.path.levels.params datum.level).clip (C.path.levels.params datum.level).width
      (C.path.levels.params datum.level).paths (C.path.levels.clock.loopCap datum.level) := by
    rw [← hs.clip]
    exact hs.good.paths
  rw [H.vacuum.representation]
  exact PreReset.append_eval _ _ _ _ _ _ _ _ _ _ hW
    H.vacuum.source_summable H.vacuum.model_summable U

/-- Only a separately proved stronger norm receipt permits the existing
stage-budget `Early` consumer. The literal qev quote itself is at the fixed
finite norm in `H.vacuum.estimate`. -/
theorem toEarly (hC : C.Makes)
    (hLocal : AnalyticBridge.VerifiedReset.Collection.Local H.vacuum.listing
      (C.path.levels.budget datum.level) H.vacuum.source
      (vacuumRate J.order K.vacuumConstant (C.S.block datum.level).val
        (K.vanishing datum.level) (K.geometry datum.level) I.inherited I.calibration
        (Currency.g C datum.cutoff datum.period (datum.level + 1)))
      (C.path.levels.clock.forcedAllowance datum.level)) :
    Early C datum.cutoff datum.period datum.level (I.plan.layers datum.level)
      H.vacuum.listing H.vacuum.source H.vacuum.scalar
      (I.plan.predict datum.level) (I.plan.alpha datum.level)
      (vacuumRate J.order K.vacuumConstant (C.S.block datum.level).val
        (K.vanishing datum.level) (K.geometry datum.level) I.inherited I.calibration
        (Currency.g C datum.cutoff datum.period (datum.level + 1)))
      (C.path.levels.clock.forcedAllowance datum.level) H.output.carrier.rep.eval where
  bud := hLocal
  exactly := funext (H.rendered_vacuum hC)

/-- The functional pointwise consumer needs its next-use price from a separate
application proof. Supplying that proof does not alter any output, root,
formal model, test, scalar, forced label, or actual trajectory. -/
def with_next_price (hC : C.Makes)
    (hInput : I.inputCarrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (hTotal : H.output.carrier.rep.activities.Valid
      (C.path.levels.budget datum.level) (C.path.levels.clock.allowance datum.level)
      (C.path.levels.clock.forcedAllowance datum.level))
    (nextRegular nextForced : ℝ)
    (hnext : FullBudget (C.path.levels.budget datum.level)
      (pullback (testInclusion J.tests) H.output.output) I.outputRadii
      (forcedDivisor C datum.level) nextRegular nextForced) :
    FunctionalMarkedReclosure Y datum I.colors (I.inputCarrier.onActual hInput)
      I.fineRoots I.coarseRoots I.input
      I.inputPackets I.inputRadii I.inputKernelCosts I.inputForcedPrice I.model
      J.order forcedOrder (A.outputNorm datum.level) I.outputRadii I.outputKernelCosts
      delta (K.markedConstant delta) (K.geometry datum.level) I.inherited I.calibration
      nextRegular nextForced I.outputAddresses where
  prepared_input := {
    convention := I.prepared.convention
    remainder := I.prepared.remainder
    regular_zero := I.prepared.regular_zero
    unit_zero := I.prepared.unit_zero
    caption_zero := I.prepared.caption_zero
    full := I.prepared.full
    forced_price := I.prepared.forced_price }
  input_kernel_positive := I.input_kernel_positive
  output_kernel_positive := I.output_kernel_positive
  carrier := H.output.carrier.onActual
    (H.output.exact.actual_output hC datum.below hInput)
  total := hTotal
  norm_threshold := (A.output_norm datum.level).threshold
  norm_block := (A.output_norm datum.level).block
  output := H.output.output
  residual := H.output.residual
  formal := I.prescribed
  exact := ⟨H.output.exact.roots, H.output.exact.density⟩
  output_multilinear := H.output.output_multilinear
  residual_multilinear := H.output.residual_multilinear
  output_addresses := H.output.output_retains
  residual_addresses := H.output.residual_retains
  full := H.output.full
  residual_price := H.residual_price
  next_price := hnext
  vacuum_reserve := H.output.vacuum_reserve

/-- Optional compatibility with the old whole-inventory locality receipt.
These two stronger proofs are not assumptions of the functional consumer. -/
def with_next_price_strong (hC : C.Makes)
    (hInput : I.inputCarrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (hTotal : H.output.carrier.rep.activities.Valid
      (C.path.levels.budget datum.level) (C.path.levels.clock.allowance datum.level)
      (C.path.levels.clock.forcedAllowance datum.level))
    (nextRegular nextForced : ℝ)
    (hnext : FullBudget (C.path.levels.budget datum.level)
      (pullback (testInclusion J.tests) H.output.output) I.outputRadii
      (forcedDivisor C datum.level) nextRegular nextForced)
    (hOutput : Retains H.output.output I.outputAddresses)
    (hResidual : Retains H.output.residual I.outputAddresses) :
    MarkedReclosure Y datum I.colors (I.inputCarrier.onActual hInput)
      I.fineRoots I.coarseRoots I.input
      I.inputPackets I.inputRadii I.inputKernelCosts I.inputForcedPrice I.model
      J.order forcedOrder (A.outputNorm datum.level) I.outputRadii I.outputKernelCosts
      delta (K.markedConstant delta) (K.geometry datum.level) I.inherited I.calibration
      nextRegular nextForced I.outputAddresses :=
  (H.with_next_price hC hInput hTotal nextRegular nextForced hnext).toStrong
    hOutput hResidual

/-- The scalar output is the original actual denominator whenever the
input is on that trajectory. The same output is used by primary extraction
and the full marked/forced estimates. -/
theorem actual_vacuum (hC : C.Makes)
    (hInput : I.inputCarrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval) :
    H.output.carrier.rep.eval = (C.path.rep datum.cutoff datum.period datum.level).eval :=
  H.output.exact.actual_output hC datum.below hInput

end Result

end YM.Integration.LocalComparison.Global
