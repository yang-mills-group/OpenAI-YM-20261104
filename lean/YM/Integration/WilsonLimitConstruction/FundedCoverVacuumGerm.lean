import YM.Integration.ActualSelectedVacuumGerm
import YM.Integration.WilsonLimitConstruction.FundedCanonicalInputPayload
import YM.Integration.WilsonLimitConstruction.FundedPhysicalCatalogue

/-! The physical unmasked reserve and retained finite action have their
original all-field splitting, kinetic germ and full requested law. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonLimitConstruction.FundedCoverVacuumGerm
open Function Filter Lattice Wilson WilsonStartup RG Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection
open AnalyticBridge.VerifiedReset.Averaging
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open ZeroAwareIntrinsicRenderInvoice
open FundedPhysicalCatalogue
open scoped Topology Classical BigOperators

variable {G : Gauge} (run : Run G)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} {A : NumericSchedule run.family J}
    {datum : LocalFormal.Datum run.family Gamma}
    {caps : Handoff.OutputCapacities}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : Real}
    {I : FullPreparedInputAt F eta_w} {M : FundedPhysicalCatalogue.Purchase caps K F}

local notation "pOut" => A.outputNorm datum.level
local notation "path" => RG.Rep.path (run.family.path.rep datum.cutoff datum.period datum.level)
local notation "profile" => run.family.path.levels.params datum.level
local notation "loopCap" => run.family.path.levels.clock.loopCap datum.level
local notation "forcedCap" => run.family.path.levels.clock.forcedAllowance datum.level

abbrev sourcePrice (input : FullPreparedInputAt F eta_w) (prices : NumericPrices A) : Real :=
  ActualSelectedVacuumGerm.sourcePrice run input prices

def regularPrice (input : FullPreparedInputAt F eta_w)
    (model : FundedPhysicalCatalogue.Purchase caps K F) : Real :=
  CappedRegularReset.regularNeed G pOut (profile).clip (profile).width (profile).paths 0
    (sourcePrice run input K) +
  Render.unitBill
    (repriceLayers (ZeroAwareCappedRenderInvoice.credit model.vacuum.packets)
      (model.plan.layers datum.level))
    (Currency.B run.family.path.levels datum.level)

variable (S : FundedRenderedBank.Chosen K I M.toCatalogue)

def shell : Rep G (run.family.side datum.level datum.period) :=
  Render.append (M.plan.layers datum.level)
    (VacuumGermReset.shell path (profile).clip pOut S.vacuum.listing S.vacuum.source
      (M.plan.predict datum.level) S.vacuum.scalar 0)
    (Render.prefactor (Currency.gain (M.plan.predict datum.level)))

def softLog (U : Config G (run.family.side datum.level datum.period)) : Real :=
  ∑' i, (Reset.reserve path (profile).clip pOut S.vacuum.listing S.vacuum.source 0
    (delta (S.vacuum.listing.read S.vacuum.source))).logarithm i U

private theorem full_eval :
    (PreReset.append (M.plan.layers datum.level) path (profile).clip pOut
      S.vacuum.listing S.vacuum.source (M.plan.predict datum.level) S.vacuum.scalar 0
      (Render.prefactor (Currency.gain (M.plan.predict datum.level)))).eval =
      S.bank.output.carrier.rep.eval := by
  exact (ActualRunVacuumGermInput.append_eval_eq
    (M.plan.layers datum.level) path (profile).clip pOut
    (run.family.path.levels.budget datum.level)
    S.vacuum.listing S.vacuum.source (M.plan.predict datum.level) S.vacuum.scalar 0
    (Render.prefactor (Currency.gain (M.plan.predict datum.level)))
    (A.output_norm datum.level).block (A.output_norm datum.level).threshold).trans
      (congrArg Rep.eval S.vacuum.representation.symm)

/-- Every field retains the full omitted soft logarithm. -/
theorem raw_eval (hG : G.Simple) (hw : Geo.Width pOut (profile).clip (profile).width)
    (U : Config G (run.family.side datum.level datum.period)) :
    (shell run S).eval U * Real.exp (softLog run S U) =
      S.bank.output.carrier.rep.eval U := by
  let base := VacuumGermReset.shell path (profile).clip pOut S.vacuum.listing
    S.vacuum.source (M.plan.predict datum.level) S.vacuum.scalar 0
  let k : Piece G (run.family.side datum.level datum.period) → ℝ :=
    Render.prefactor (Currency.gain (M.plan.predict datum.level))
  have hn := ActualRunVacuumGermInput.period_room run datum.level datum.period
  have hl := CappedRegularReset.lawful hG hn (FundedCanonicalInputPayload.path_bounds run (datum := datum))
    S.vacuum.estimate (FundedCanonicalInputPayload.decent run (A := A) (datum := datum)) hw (M.plan.predict datum.level) S.vacuum.scalar 0
  have hr := VacuumGermReset.raw_eval hG hn (FundedCanonicalInputPayload.path_bounds run (datum := datum)) S.vacuum.estimate
    (FundedCanonicalInputPayload.decent run (A := A) (datum := datum)) hw (M.plan.predict datum.level) S.vacuum.scalar 0 U
  have hp := PreReset.append_eval (M.plan.layers datum.level) path (profile).clip pOut
    S.vacuum.listing S.vacuum.source (M.plan.predict datum.level) S.vacuum.scalar 0 k
    (FundedCanonicalInputPayload.path_bounds run (datum := datum)) (fun U => PreReset.series_of_EBound S.vacuum.estimate.unweighted U)
    (fun a ha U => PreReset.payload_series (M.output_layers_paid a ha)
      (S.vacuum.listing.read S.vacuum.source) U) U
  calc
    _ = (base.eval U * Real.exp (-Render.renders k pOut U (M.plan.layers datum.level))) *
        Real.exp (softLog run S U) :=
      congrArg (fun z => z * Real.exp (softLog run S U))
        (Render.generated k M.output_layers_paid hl.labels U)
    _ = (base.eval U * Real.exp (softLog run S U)) *
        Real.exp (-Render.renders k pOut U (M.plan.layers datum.level)) := by ring
    _ = Reset.supplied path (profile).clip pOut S.vacuum.listing S.vacuum.source
        (M.plan.predict datum.level) S.vacuum.scalar 0 U *
        Real.exp (-Render.renders k pOut U (M.plan.layers datum.level)) :=
      congrArg (fun z => z * Real.exp (-Render.renders k pOut U
        (M.plan.layers datum.level))) hr
    _ = _ := hp.symm.trans (congrFun (full_eval run S) U)

/-- The good-field equality uses native vanishing of that exact logarithm. -/
theorem good_eval (hG : G.Simple) (hw : Geo.Width pOut (profile).clip (profile).width)
    (U : Config G (run.family.side datum.level datum.period))
    (hU : flags (pOut).threshold U = ∅) :
    (shell run S).eval U = S.bank.output.carrier.rep.eval U := by
  exact ActualVacuumRenderedGerm.good_eq hG
    (ActualRunVacuumGermInput.period_room run datum.level datum.period)
    (FundedCanonicalInputPayload.path_bounds run (datum := datum)) S.vacuum.estimate (FundedCanonicalInputPayload.decent run (A := A) (datum := datum)) hw
    (M.plan.layers datum.level)
    (Render.prefactor (Currency.gain (M.plan.predict datum.level)))
    M.output_layers_paid (M.plan.predict datum.level) S.vacuum.scalar 0
    (A.output_norm datum.level).block (A.output_norm datum.level).threshold
    (congrArg Rep.eval S.vacuum.representation.symm) U hU

/-- Only the supplied incoming actual-vacuum attachment is transported. -/
theorem kinetic_germ (hG : G.Simple) (hw : Geo.Width pOut (profile).clip (profile).width)
    (hFine : I.carrier.rep.eval =
      (run.family.path.rep datum.cutoff datum.period (datum.level + 1)).eval) :
    ∀ c : G.Color, ‖c‖ = 1 → ∀ b : Bool, ∀ᶠ t : Real in 𝓝 0,
      (shell run S).eval (line (Pert.Kinetic.rowWave c b) t) =
        (run.family.path.rep datum.cutoff datum.period datum.level).eval
          (line (Pert.Kinetic.rowWave c b) t) := by
  intro c _hc b
  filter_upwards [Pert.Kinetic.rays_free (pOut).threshold (pOut).threshold_pos
    (Pert.Kinetic.rowWave c b)] with t ht
  exact (good_eval run S hG hw _ ht).trans
    (congrFun (S.bank.output.output_vacuum run.makes datum.below hFine) _)

/-- Intrinsic repricing changes no actual layer, occurrence or forced activity. -/
theorem lawful (hG : G.Simple) (hw : Geo.Width pOut (profile).clip (profile).width)
    (hstripe : M.plan.predict datum.level ∈
      Currency.stripe (Currency.B run.family.path.levels datum.level)) :
    (shell run S).Lawful (profile).width (profile).paths loopCap
      (regularPrice run I M) forcedCap := by
  have hl := CappedRegularReset.lawful hG
    (ActualRunVacuumGermInput.period_room run datum.level datum.period)
    (FundedCanonicalInputPayload.path_bounds run (datum := datum)) S.vacuum.estimate (FundedCanonicalInputPayload.decent run (A := A) (datum := datum)) hw
    (M.plan.predict datum.level) S.vacuum.scalar 0
  refine ⟨FundedCanonicalInputPayload.path_bounds run (datum := datum), ?_⟩
  exact SelectedPlanIntrinsicRenderValidity.unit_valid M.vacuum.packets
    M.output_layers_paid (A.output_width_pos datum.level)
    (WardBin.hot run.family.path.levels datum.level) hstripe _ hl.labels

/-- The shell beta includes the source's actual affine extraction. -/
theorem beta :
    (shell run S).beta = M.plan.predict datum.level +
      delta (S.vacuum.listing.read S.vacuum.source) := by
  change M.plan.predict datum.level + 0 +
    delta (S.vacuum.listing.read S.vacuum.source) = _
  rw [add_zero]

end YM.Integration.WilsonLimitConstruction.FundedCoverVacuumGerm
end
