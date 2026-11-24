import YM.Integration.FullQLocalCanonicalForcedOutput
import YM.Integration.ActualSelectedVacuumGerm
import YM.Integration.NativeCanonicalResetNorm
import YM.Integration.NativeRequestedInputNorm
import YM.Integration.NativePreResetExponent
import YM.Push.BETA_TRANSPORT.Curve

/-! The regular remainder on the final canonical carrier.
The fixed drawer reindexes the pre-fusion shell's complete regular rows.
Only the kinetic coefficient discrepancy is placed in calibration; the full
soft logarithm remains in the carrier's forced merger. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualCanonicalInputPayload
open Function Filter Lattice Wilson WilsonStartup RG Marker
open PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch
open IterationFour IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection
open AnalyticBridge.VerifiedReset.Averaging
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Canonical Progress.DirectedRecipe Ovens Ovens.Pipes
open ActualRunAdmissionScales OriginalRunConstruction
open scoped Topology Classical BigOperators

variable {G : Gauge}

/-- The drawer changes addresses, while preserving every old regular row
and adding only zero rows. No forced-fusion estimate is used. -/
private theorem after_receipts {n : Side} (W : PathData G) (c : Clip)
    (p : BudgetPoint) (X : Listing G n) (v : Collection.Source G n)
    (beta tau : Real) {d w : Real}
    (h : (VacuumGermReset.shell W c p X v beta tau 0).activities.Valid p d w) :
    (NativeRequestedInputNorm.regularPayload
      (Reset.after W c p X v beta tau 0).activities).Invoice p d ∧
      (Reset.after W c p X v beta tau 0).activities.EBound p d := by
  let Y := shelves X W p
  let T := Reset.reserve W c p X v 0 (delta (X.read v))
  have h0 : (Y.pours T).Valid p d w := h
  have hr := (Rack.preserves Y T p).regular h0.regular
  have hb := (Rack.preserves Y T p).Ebound h0.boundE
  refine ⟨?_, hb⟩
  refine {
    smooth := hr.smooth
    flat := hr.at_flat
    null := hr.vanish
    moves := ?_
    credit := hb }
  intro s b
  obtain ⟨e⟩ := h0.moves s b
  let e' := on_shelves e
  exact ⟨e'.ep, fun i => ⟨e'.reg_site i, e'.reg_support i, e'.valuesE i⟩⟩

private theorem renders_same_threshold {n : Side} (S : List (Piece G n))
    (k : Piece G n → Real) (p q : BudgetPoint) (h : p.threshold = q.threshold)
    (U : Config G n) : Render.renders k p U S = Render.renders k q U S := by
  induction S with
  | nil => rfl
  | cons a l ih =>
    change k a * a.packet.amount p U + Render.renders k p U l =
      k a * a.packet.amount q U + Render.renders k q U l
    rw [NativeRequestedInputNorm.amount_eq a.packet h U, ih]

section Actual
variable (run : Run G)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} {A : NumericSchedule run.family J}
    {datum : LocalFormal.Datum run.family Gamma}
    {caps : Handoff.OutputCapacities}
    {Y : YM.Comparison.RG02.Bulk.Chain run.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : Real}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}

local notation "pOut" => A.outputNorm datum.level
local notation "pNative" => run.family.path.levels.budget datum.level
local notation "path" => RG.Rep.path (run.family.path.rep datum.cutoff datum.period datum.level)
local notation "profile" => run.family.path.levels.params datum.level
local notation "loopCap" => run.family.path.levels.clock.loopCap datum.level
local notation "forcedCap" => run.family.path.levels.clock.forcedAllowance datum.level

variable (S : Retained.Chosen K I M)

/-- The full fused base, before appending the same selected model list. -/
def base : Rep G (run.family.side datum.level datum.period) :=
  Reset.after path (profile).clip pNative S.vacuum.listing S.vacuum.source
    (M.plan.predict datum.level) S.vacuum.scalar 0

/-- Exactly the final base's regular rows, including the drawer's zero rows. -/
def error : Payload G (run.family.side datum.level datum.period) :=
  NativeRequestedInputNorm.regularPayload (base run S).activities

/-- The original capped regular-reset invoice, without any model or gas bill. -/
def errorPrice (input : FullPreparedInputAt F eta_w) (prices : NumericPrices A) : Real :=
  CappedRegularReset.regularNeed G pOut (profile).clip (profile).width
    (profile).paths 0 (ActualSelectedVacuumGerm.sourcePrice run input prices)

private theorem error_output :
    error run S = NativeRequestedInputNorm.regularPayload
      (Reset.after path (profile).clip pOut S.vacuum.listing S.vacuum.source
        (M.plan.predict datum.level) S.vacuum.scalar 0).activities := by
  have h := congrArg (fun Q : Rep G (run.family.side datum.level datum.period) =>
    NativeRequestedInputNorm.regularPayload Q.activities)
    (NativeCanonicalResetNorm.after_budget_eq path (profile).clip pNative pOut
      S.vacuum.listing S.vacuum.source (M.plan.predict datum.level) S.vacuum.scalar 0
      (A.output_norm datum.level).block.symm (A.output_norm datum.level).threshold.symm)
  exact h

omit [Fintype V] in
private theorem path_bounds :
    (path).Bounds (profile).clip (profile).width (profile).paths loopCap := by
  have hs : run.family.path.Conv datum.cutoff datum.period datum.level :=
    run.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le
  rw [← hs.clip]
  exact hs.good.paths

omit [Fintype V] in
private theorem decent : Decent (profile).clip pOut := by
  have h := (ActualRunRequestedWidth.native_geometry run datum.level).1
  exact ⟨h.direct, by simpa only [(A.output_norm datum.level).block] using h.radius,
    by simpa only [(A.output_norm datum.level).block,
      (A.output_norm datum.level).threshold] using h.cut⟩

private theorem shell_lawful (hG : G.Simple)
    (hw : Geo.Width pOut (profile).clip (profile).width) :
    (VacuumGermReset.shell path (profile).clip pOut S.vacuum.listing
      S.vacuum.source (M.plan.predict datum.level) S.vacuum.scalar 0).Lawful
      (profile).width (profile).paths loopCap (errorPrice run I K) forcedCap :=
  CappedRegularReset.lawful hG
    (ActualRunVacuumGermInput.period_room run datum.level datum.period)
    (path_bounds run) S.vacuum.estimate (decent run) hw
    (M.plan.predict datum.level) S.vacuum.scalar 0

/-- The full base remainder is flat and affine-null at every genuinely weaker
requested norm. Only non-strict support/order restriction is required. -/
theorem invoice (hG : G.Simple)
    (hw : Geo.Width pOut (profile).clip (profile).width)
    (p : BudgetPoint) (hthreshold : p.threshold = (pOut).threshold)
    (hblock : p.B = (pOut).B) (horder : p.order ≤ (pOut).order)
    (hpower : p.power ≤ (pOut).power)
    (hsupport : p.supportExponent ≤ (pOut).supportExponent) :
    (error run S).Invoice p (errorPrice run I K) := by
  have h := after_receipts path (profile).clip pOut S.vacuum.listing
    S.vacuum.source (M.plan.predict datum.level) S.vacuum.scalar
    (shell_lawful run S hG hw).labels
  rw [error_output run S]
  exact NativeRequestedInputNorm.invoice_restrict h.1
    hthreshold hblock horder hpower hsupport

/-- The exact final exponent keeps every masked model row and the full
regular remainder. The only calibration is the actual kinetic discrepancy. -/
theorem exponent (P : CanonicalOutput S) (hG : G.Simple)
    (hw : Geo.Width pOut (profile).clip (profile).width)
    (p : BudgetPoint) (hthreshold : p.threshold = (pOut).threshold)
    {eta : Real} (C : CalibrationPresentation P.output.carrier.rep p eta)
    (hC : ∀ U, C.amount U =
      (P.output.carrier.rep.beta -
        run.family.path.β datum.cutoff datum.period datum.level) *
      Push.BetaTransport.kinetic path (profile).clip p U)
    (U : Config G (run.family.side datum.level datum.period)) :
    P.output.carrier.rep.exponent U = P.output.carrier.rep.scalar -
      ((path).inChannels (profile).clip P.output.carrier.rep.p
        (run.family.path.β datum.cutoff datum.period datum.level) U +
      Render.renders (Render.prefactor (Currency.gain (M.plan.predict datum.level)))
        P.output.carrier.rep.p U (M.plan.layers datum.level)) -
      (error run S).amount p U - C.amount U := by
  let Q := Reset.after path (profile).clip pOut S.vacuum.listing S.vacuum.source
    (M.plan.predict datum.level) S.vacuum.scalar 0
  let k : Piece G (run.family.side datum.level datum.period) → ℝ := Render.prefactor (Currency.gain (M.plan.predict datum.level))
  let beta := run.family.path.β datum.cutoff datum.period datum.level
  have h := after_receipts path (profile).clip pOut S.vacuum.listing
    S.vacuum.source (M.plan.predict datum.level) S.vacuum.scalar
    (shell_lawful run S hG hw).labels
  have hAppend : (Render.append (M.plan.layers datum.level) Q k).exponent U =
      Q.exponent U - Render.renders k pOut U (M.plan.layers datum.level) :=
    NativePreResetExponent.append_exponent (M.plan.layers datum.level) Q k
      (fun U => PreReset.series_of_EBound h.2 U)
      (fun a ha U => PreReset.payload_series (M.output_layers_paid a ha) Q.activities U) U
  have hNative : P.output.carrier.rep.exponent U =
      (Render.append (M.plan.layers datum.level) Q k).exponent U := by
    rw [P.representation]
    exact NativeCanonicalResetNorm.append_exponent_eq
      (M.plan.layers datum.level) path (profile).clip pNative pOut
      S.vacuum.listing S.vacuum.source (M.plan.predict datum.level) S.vacuum.scalar 0 k
      (A.output_norm datum.level).block.symm
      (A.output_norm datum.level).threshold.symm U
  have hReset := NativeCanonicalResetNorm.after_budget_eq path (profile).clip pNative pOut
    S.vacuum.listing S.vacuum.source (M.plan.predict datum.level) S.vacuum.scalar 0
    (A.output_norm datum.level).block.symm (A.output_norm datum.level).threshold.symm
  have hs := congrArg Rep.scalar hReset
  have hb := congrArg Rep.beta hReset
  have hScalar : P.output.carrier.rep.scalar = Q.scalar :=
    (congrArg Rep.scalar P.representation).trans hs
  have hBeta : P.output.carrier.rep.beta = Q.beta :=
    (congrArg Rep.beta P.representation).trans hb
  have hPoint : P.output.carrier.rep.p = pNative :=
    congrArg Rep.p P.representation
  have hError : (error run S).amount p U = Q.activities.additive pOut U := by
    rw [error_output run S]
    exact NativeRequestedInputNorm.regular_amount Q.activities hthreshold U
  have hKinetic : Push.BetaTransport.kinetic path (profile).clip p U =
      Push.BetaTransport.kinetic path (profile).clip pOut U := by
    simp only [Push.BetaTransport.kinetic, PathData.baseTerm,
      PathData.atomSeries, Atom.placed, hthreshold]
  have hCalibration : C.amount U =
      (Q.beta - beta) * Push.BetaTransport.kinetic path (profile).clip pOut U := by
    rw [hC U, hBeta, hKinetic]
  have hChannels : (path).inChannels (profile).clip P.output.carrier.rep.p beta U =
      (path).inChannels (profile).clip pOut beta U := by
    rw [hPoint]
    exact NativePreResetExponent.channels_same_threshold path (profile).clip
      pNative pOut (A.output_norm datum.level).threshold.symm beta U
  have hRenders : Render.renders k P.output.carrier.rep.p U (M.plan.layers datum.level) =
      Render.renders k pOut U (M.plan.layers datum.level) := by
    rw [hPoint]
    exact renders_same_threshold (M.plan.layers datum.level) k pNative pOut
      (A.output_norm datum.level).threshold.symm U
  rw [hNative, hAppend, hScalar, hChannels, hRenders, hError, hCalibration]
  change Q.scalar - (path).inChannels (profile).clip pOut Q.beta U -
      Q.activities.additive pOut U - Render.renders k pOut U (M.plan.layers datum.level) =
    Q.scalar - ((path).inChannels (profile).clip pOut beta U +
      Render.renders k pOut U (M.plan.layers datum.level)) -
      Q.activities.additive pOut U -
      (Q.beta - beta) * Push.BetaTransport.kinetic path (profile).clip pOut U
  rw [Push.BetaTransport.channels_split U Q.beta, Push.BetaTransport.channels_split U beta]
  ring

end Actual

/-- One actual geometry tail pays the same full base remainder at every
requested norm covered by the output order, distance and support bounds. -/
theorem eventually_invoice (run : Run G) (hG : G.Simple)
    (hprofile : WithStage run.metals.p originalOrders)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V} {J : Request V}
    (caps : Handoff.OutputCapacities) (A : NumericSchedule run.family J)
    (K : NumericPrices A) :
    ∀ᶠ m : Nat in atTop,
      ∀ (datum : LocalFormal.Datum run.family Gamma), datum.level = m →
      ∀ (Y : YM.Comparison.RG02.Bulk.Chain run.family.path)
        (F : AnalyticInput J A datum) (eta_w : Real)
        (I : FullPreparedInputAt F eta_w) (M : AnalyticOutput caps Y K F)
        (S : Retained.Chosen K I M) (p : BudgetPoint),
      p.threshold = (A.outputNorm datum.level).threshold →
      p.B = (A.outputNorm datum.level).B →
      p.order ≤ (A.outputNorm datum.level).order →
      p.power ≤ (A.outputNorm datum.level).power →
      p.supportExponent ≤ (A.outputNorm datum.level).supportExponent →
      (error run S).Invoice p (errorPrice run I K) := by
  filter_upwards [ActualRunRequestedWidth.eventually_geometry run hprofile
    J.outputFieldOrder J.outputDistanceOrder J.outputSupport
    J.field_minimum J.distance_minimum J.output_support_pos] with m hm
  intro datum hlevel Y F eta_w I M S p ht hb ho hp hs
  subst m
  have hEq : A.outputNorm datum.level =
      requestedBudget run.family.path.levels datum.level
        J.outputFieldOrder J.outputDistanceOrder J.outputSupport
        J.field_minimum J.distance_minimum J.output_support_pos :=
    ActualRepeatedNorm.norm_unique run.family J.outputFieldOrder
      J.outputDistanceOrder J.outputSupport J.field_minimum J.distance_minimum
      J.output_support_pos datum.level (A.outputNorm datum.level)
      (A.output_norm datum.level)
  have hw : Geo.Width (A.outputNorm datum.level)
      (run.family.path.levels.params datum.level).clip
      (run.family.path.levels.params datum.level).width := by
    rw [hEq]
    exact hm.2
  exact invoice run S hG hw p ht hb ho hp hs

end YM.Integration.ActualCanonicalInputPayload
end
