import YM.Integration.ActualNextRetunedFineAction
import YM.Integration.ActualRetunedVacuumGradedCost
import YM.Integration.FullQLocalPrescribedWidth
import YM.Integration.FullQLocalSuccessiveRequests

/-!
The next analytic input uses the previous selected model's complete retuned
list, finite interpolated packet and original output addresses. The bridge
receipts are explicit: the prescribed width is the next input width, the
new cost pays the original geometric bill, and the native orders are
admitted. The same-family chain supplies these receipts separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualNextAnalyticInput
open Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.PreRun.SuccessiveRequests
open scoped Classical

variable {G : Gauge} {V : Type} [DecidableEq V]
    {Gamma : Census V} {J : Request V}

omit [DecidableEq V] in
private def castRegion {a b : Side} (h : a = b)
    (R : Comparison.Density.Testing.Region (fun v => (J.tests v).Mood) a) :
    Comparison.Density.Testing.Region (fun v => (J.tests v).Mood) b := h ▸ R

private theorem castPermits {a b : Side} (h : a = b)
    {L : List (Piece G a)} {p : BudgetPoint} (H : Render.permits L p) :
    Render.permits (h ▸ L) p := by
  cases h
  exact H

private def castGraded {a b : Side} (h : a = b)
    {L : List (Piece G a)} {p : BudgetPoint} {order rankCap : ℕ}
    {width budget : ℝ} (H : GradedVacuumLayers L p order rankCap width budget) :
    GradedVacuumLayers (h ▸ L) p order rankCap width budget := by
  cases h
  exact H

private theorem castRank {a b : Side} (h : a = b)
    (P : MarkedPackets J.tests G a Gamma) :
    (h ▸ P : MarkedPackets J.tests G b Gamma).rankCap = P.rankCap := by
  cases h
  rfl

private theorem castPower {a b : Side} (h : a = b)
    (P : MarkedPackets J.tests G a Gamma) :
    (h ▸ P : MarkedPackets J.tests G b Gamma).powerCap = P.powerCap := by
  cases h
  rfl

private theorem castPaid {a b : Side} (h : a = b)
    {P : MarkedPackets J.tests G a Gamma} {p : BudgetPoint}
    {address : V → Support a}
    {region : Comparison.Density.Testing.Region (fun v => (J.tests v).Mood) a}
    {w : V → ℝ} {g width budget : ℝ} {offset slope : ℕ}
    (H : P.Paid p address region w g width budget offset slope) :
    (h ▸ P : MarkedPackets J.tests G b Gamma).Paid p
      (fun v => cast (congrArg Support h) (address v)) (castRegion h region)
      w g width budget offset slope := by
  cases h
  exact H

private def enlargeGraded {a : Side} {L : List (Piece G a)}
    {p : BudgetPoint} {order rankCap nextCap : ℕ} {width budget nextBudget : ℝ}
    (H : GradedVacuumLayers L p order rankCap width budget)
    (hc : rankCap ≤ nextCap) (hb : budget ≤ nextBudget) :
    GradedVacuumLayers L p order nextCap width nextBudget where
  packets := { H.packets with
    rank_bounded := fun a ha => (H.packets.rank_bounded a ha).trans hc
    total := H.packets.total.trans hb
    cover_cost := H.packets.cover_cost.trans hb }
  orders := H.orders
  leading_rank := H.leading_rank

private theorem enlargePaid {a : Side} {P : MarkedPackets J.tests G a Gamma}
    {p : BudgetPoint} {address : V → Support a}
    {region : Comparison.Density.Testing.Region (fun v => (J.tests v).Mood) a}
    {w : V → ℝ} {g width budget nextBudget : ℝ} {offset slope : ℕ}
    (H : P.Paid p address region w g width budget offset slope)
    (hb : budget ≤ nextBudget) :
    P.Paid p address region w g width nextBudget offset slope :=
  { H with roots := fun v =>
      ⟨(H.roots v).1, (H.roots v).2.1, (H.roots v).2.2.trans hb⟩ }

variable [Fintype V]

private def fineAction {C : Family G} {D : LocalFormal.Datum C Gamma}
    {W : TestSpace J.tests → Bulk.Colors Gamma G (C.side (D.level + 1) D.period)}
    {L : List (Piece G (C.side (D.level + 1) D.period))}
    (H : FineWholeAction J D W L) (caps : Handoff.OutputCapacities) (r : ℕ) :
    FineWholeAction (nextRequest J caps r) D W L where
  standard := H.standard
  input_summable := H.input_summable
  inputExtension := H.inputExtension
  formalInputExtension := H.formalInputExtension
  input_extension_value := H.input_extension_value
  formal_input_extension_value := H.formal_input_extension_value
  input_extension_smooth := H.input_extension_smooth
  formal_input_extension_smooth := H.formal_input_extension_smooth
  input_whole := H.input_whole

omit [DecidableEq V] [Fintype V] in
/-- Only the native finite-order and original primary-address admissions. -/
structure Eligibility (C : Family G) (J : Request V) (m : ℕ) : Prop where
  input_field : J.inputFieldOrder ≤ (C.path.levels.budget (m + 1)).order
  input_distance : J.inputDistanceOrder ≤ (C.path.levels.budget (m + 1)).power
  output_field : J.outputFieldOrder ≤ (C.path.levels.budget m).order
  output_distance : J.outputDistanceOrder ≤ (C.path.levels.budget m).power
  primary v : C.ref (J.outputWeight v) ≤ m

variable (run : Run G) {A : NumericSchedule run.family J}
    {datum : LocalFormal.Datum run.family Gamma}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain run.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum}
    {eta_w : ℝ} {I : FullPreparedInputAt F eta_w}
    {M : AnalyticOutput caps Y K F}

/-- Construct the next input from literal, already-paid bridge receipts.
No old output width is identified with a newly selected width. -/
def build (S : Retained.Chosen K I M) (r : ℕ) {m : ℕ}
    (hm : datum.level = m + 1)
    (A' : NumericSchedule run.family (nextRequest J caps r))
    (W : Bulk.Colors Gamma G (run.family.side (m + 1) datum.period))
    (x : Exterior.fieldDir G (run.family.side m datum.period) 1)
    (width : ℕ → ℝ) (H : Prescribed.WidthReceipt width M)
    (hnorm : A'.inputNorm m = A.outputNorm datum.level)
    (hwidth : width datum.level = A'.inputWidth m)
    (hcost : (4 : ℝ)^J.order * K.geometry datum.level ≤ A'.admittedCost m)
    (hlo : (1/4 : ℝ) ≤ ActualRunRetunedVacuum.ratio run M)
    (hhi : ActualRunRetunedVacuum.ratio run M ≤ 4)
    (hpaid : (ActualRunInterpolatedPackets.onRun run datum.cutoff datum.period
        datum.level S.output.model r).Paid
      (A.outputNorm datum.level) F.outputAddresses M.region
      (fun v => F.outputRadii v / F.kernelCosts v)
      (Pert.Asymptotics.regulatorRun run.family datum.cutoff datum.period datum.level)
      (width datum.level) (K.geometry datum.level * 2) M.coverOffset M.coverSlope)
    (eligible : Eligibility run.family J m) :
    AnalyticInput (nextRequest J caps r) A'
      (ActualNextLocalDatum.descend datum hm W x) := by
  let hs := congrArg (fun n => run.family.side n datum.period) hm
  have hcaps := nextRequest_caps J caps r
  have htwo : (2 : ℝ) ≤ (4 : ℝ)^J.order := by
    calc
      (2 : ℝ) ≤ (4 : ℝ)^2 := by norm_num
      _ ≤ (4 : ℝ)^J.order := pow_le_pow_right₀ (by norm_num) J.order_ge_two
  have hpacketCost : K.geometry datum.level * 2 ≤ A'.admittedCost m := by
    calc
      K.geometry datum.level * 2 = 2 * K.geometry datum.level := by ring
      _ ≤ (4 : ℝ)^J.order * K.geometry datum.level :=
        mul_le_mul_of_nonneg_right htwo (K.geometry_nonnegative datum.level)
      _ ≤ A'.admittedCost m := hcost
  have hgeometry : K.geometry datum.level ≤ A'.admittedCost m := by
    calc
      K.geometry datum.level ≤ (4 : ℝ)^J.order * K.geometry datum.level :=
        le_mul_of_one_le_left (K.geometry_nonnegative datum.level)
          ((by norm_num : (1 : ℝ) ≤ 2).trans htwo)
      _ ≤ A'.admittedCost m := hcost
  let hg := enlargeGraded
    (ActualRetunedVacuumUniformCost.graded H.vacuum J.order_ge_two hlo hhi)
    hcaps.1 hcost
  have hvacuum :
      GradedVacuumLayers (ActualNextRetunedFineAction.layers run M hm)
        (A'.inputNorm m) J.order (nextRequest J caps r).vacuumRankCap
        (A'.inputWidth m) (A'.admittedCost m) := by
    rw [hnorm, ← hwidth]
    exact castGraded hs hg
  have hp :
      (ActualNextRetunedFineAction.packets run S r hm).Paid (A'.inputNorm m)
        (ActualNextLocalDatum.fineAddresses F hm) (castRegion hs M.region)
        (fun v => F.outputRadii v / F.kernelCosts v)
        (Pert.Asymptotics.regulatorRun run.family datum.cutoff datum.period (m + 1))
        (A'.inputWidth m) (A'.admittedCost m) M.coverOffset M.coverSlope := by
    rw [hnorm, ← hwidth]
    rw [← congrArg (Pert.Asymptotics.regulatorRun run.family datum.cutoff datum.period) hm]
    exact castPaid hs (enlargePaid hpaid hpacketCost)
  exact {
    whole_tests := F.whole_tests
    layers := ActualNextRetunedFineAction.layers run M hm
    layers_paid := by
      change Render.permits (ActualNextRetunedFineAction.layers run M hm) (A'.inputNorm m)
      rw [hnorm]
      exact castPermits hs (ActualRunRetunedVacuum.permits run (M := M))
    vacuum := hvacuum
    fineRoots := ActualNextLocalDatum.fineRoots F hm
    coarseRoots := ActualNextLocalDatum.coarseRoots F hm
    roots := ActualNextLocalDatum.roots F hm
    colors := ActualNextRetunedFineAction.colors run S r hm
    packets := ActualNextRetunedFineAction.packets run S r hm
    convention := ActualNextRetunedFineAction.input_colors run S r hm
    rank_bounded := by
      change (ActualNextRetunedFineAction.packets run S r hm).rankCap ≤
        (nextRequest J caps r).inputPacketRankCap
      calc
        _ = S.output.model.rankCap := castRank hs (ActualRunInterpolatedPackets.onRun
          run datum.cutoff datum.period datum.level S.output.model r)
        _ = M.model.rankCap := congrArg (fun P => P.rankCap) S.same_model
        _ ≤ caps.packetRank := M.rank_bounded
        _ ≤ _ := hcaps.2.1
    power_bounded := by
      change (ActualNextRetunedFineAction.packets run S r hm).powerCap ≤
        (nextRequest J caps r).inputPacketPowerCap
      calc
        _ = max S.output.model.powerCap (r + 2) := castPower hs (ActualRunInterpolatedPackets.onRun
          run datum.cutoff datum.period datum.level S.output.model r)
        _ = max M.model.powerCap (r + 2) :=
          congrArg (fun P => max P.powerCap (r + 2)) S.same_model
        _ ≤ _ := max_le (M.power_bounded.trans hcaps.2.2.1) hcaps.2.2.2
    whole_input := fineAction
      (Classical.choice (ActualNextRetunedFineAction.whole_action run S r hm W x)) caps r
    inputRadii := F.outputRadii
    outputRadii := fun v => F.outputRadii v / A'.radiusLoss m
    kernelCosts := F.kernelCosts
    input_radius_positive := F.output_radius_positive
    output_radius_positive := fun v =>
      div_pos (F.output_radius_positive v) (A'.radius_loss_positive m)
    kernel_positive := F.kernel_positive
    radius_admission := fun v =>
      le_of_eq (div_mul_cancel₀ (F.outputRadii v) (A'.radius_loss_positive m).ne')
    inputAddresses := ActualNextLocalDatum.fineAddresses F hm
    input_origins := ActualNextLocalDatum.fine_roots_mem F hm
    inputRegion := castRegion hs M.region
    coverOffset := M.coverOffset
    coverSlope := M.coverSlope
    cover_cost := by
      change Real.exp ((A'.inputNorm m).supportExponent * (M.coverOffset : ℝ)) ≤
        A'.admittedCost m
      rw [hnorm]
      exact M.cover_cost.trans hgeometry
    input_paid := hp
    physical_period := F.physical_period
    input_field_admitted := eligible.input_field
    input_distance_admitted := eligible.input_distance
    output_field_admitted := eligible.output_field
    output_distance_admitted := eligible.output_distance
    primary_admitted := eligible.primary }

end YM.Integration.ActualNextAnalyticInput
end
