import YM.Integration.WilsonInvariantActionPreviousQMoment
import YM.Integration.WilsonInvariantActionPreviousQTariff

/-! The independent high coupling degrees paired with the earlier centered
Wilson operator for the genuine moving grade-four measurement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionReportedQMoment
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker OPE.Therm Comparison.RG02
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Pert.Asymptotics
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalRegularConditional ManuscriptQLocalSourceFourier
open RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations Source RG3.Script.Picnic PhysicalNext.ThroughLaunch WilsonLimitConstruction
open Actual Order IterationFour IterationFour.Vacuum
open WilsonInvariantActionTransportedOld WilsonInvariantActionMixedMaterial
open RG16 PertExtension Tree Precision RG17 RG12 Extraction Spec OPE Table SharpGram.Lenses Pier.Lair Overlay PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {B:MS.Local.Physical.Deck G}
  (R:Run G) (simple:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
local notation "JB" => ActualOriginalQPointSetup.request R u J
local notation "AB" => ActualOriginalQInitialInput.schedule R simple u J A
local notation "census₀" => Stock.census V

private theorem complete {D K:ℕ} (P:Polynomial ℂ) (degree:P.natDegree ≤ D) (height:D ≤ K) :
    ManuscriptQLocalConditionalGradeTail.low P D K=P.eval 1:=by
  unfold ManuscriptQLocalConditionalGradeTail.low
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le degree)]
  rw [←Fin.sum_univ_eq_sum_range (fun i:ℕ=>P.coeff i*(1:ℂ)^i) (D+1)]
  exact Finset.sum_congr rfl fun i _=>by simp [((Nat.le_of_lt_succ i.isLt).trans height)]

variable {f:Extraction.Order} {S:Table R.family.book} (Φ:Spec.Final R.family f S) (L:RG17.Layout Φ)
    (E:OPE.Services R.family f S)

set_option backward.isDefEq.respectTransparency false in
include E in
theorem original (warm:Poetry R.family.path.levels)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (q h H:ℕ) {ε:ℝ} (positive:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀(d:LocalFormal.Datum R.family census₀),d.level=m→
    ∀(Q:MS.Land.Prescription B) (o:V→Site (R.family.side (d.level+1) d.period)) (strength:ℝ) (orders:V→ℕ)
      (stages:WithStage R.metals.p OriginalRunConstruction.originalOrders)
      (beginning:ActualOriginalQInitialPreparation.start R simple u J A stages ≤ d.level)
      (period:(JB).physicalPeriodLower ≤ (R.family.S.period d.period).val)
      (x:IndependentTests (JB).tests) (s:(census₀).Mode),
    let F:=ActualOriginalQInitialPreparation.analyticInput R simple u J A d Q o strength orders stages beginning period
    let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
    let B₀:=(R.family.path.rep d.cutoff d.period (d.level+1)).p
    let w:=fun v=>F.inputRadii v/F.kernelCosts v
    let phase z U:=Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source F.packets B₀ g x) z)
    let raw:=ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=d.cutoff)
      (F.packets.read (testInclusion (JB).tests x) g)
    let μ:=scene R.family.path d.cutoff d.period d.level
    Measurable (fun U=>(phase 1 U).part s) ∧
      ∀ (r:ℝ) (w₀:R.family.label 4) (M:ℝ), 0 ≤ M →
        R.family.ref 4 ≤ L.level r → L.level r ≤ d.level+1 →
        R.family.S.a (L.level r)/R.family.S.a (d.level+1) ≤ R.family.path.levels.clock.hatBeta (d.level+1)^H →
        mass R.family 4 (L.shift 4 r w₀) ≤ R.family.path.levels.clock.hatBeta (L.level r)^h*M →
        ∀ (y:Site (R.family.side (d.level+1) d.period)) (I:Set ℕ),
          ‖∫U,((Poly.toll w s:ℂ)*((raw U).part s-(phase 1 U).part s))*
               centered R (Nat.le_succ _) d.below (RG17.atRef L 4 r (d.cutoff,d.period) w₀) y I U ∂μ‖ ≤
            ε*g^q*M:=by
  let cap:=Fintype.card V*((JB).inputPacketPowerCap+(JB).inputPacketRankCap)
  let K:=q+2*(h+cap+H*(4+1)+1)+1
  let C:=ManuscriptQLocalRegularCalendar.constant (J:=JB) (census₀)
  have q₀ : 0 ≤ connectedBill (census₀) (Fintype.card V) := ManuscriptQLocalRegularCalendar.log_pos _
    (mul_nonneg (Nat.cast_nonneg _) (ManuscriptQLocalRegularCalendar.exp_pos _ (Nat.cast_nonneg _)))
  have cp : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) q₀
  have height:=WilsonInvariantActionPreviousQMoment.purchased R simple u J A warm K (δ:=1) zero_lt_one
  have costs:=WilsonInvariantActionPreviousQTariff.reported R Φ L E simple slow q (h+cap) H
    (show 0 ≤ 1+C by linarith) positive
  filter_upwards [height,costs] with m old pay
  intro d same Q o strength orders stages beginning period x s F g B₀ w phase raw μ
  let D:=ManuscriptQLocalShiftLedger.weight (fun _:V=>F.packets.powerCap+F.packets.rankCap) s
  obtain ⟨P,degree,eval,meas,bill⟩:=old d same Q o strength orders stages beginning period x s
  have within : D ≤ cap:=by
    dsimp only [D,cap,ManuscriptQLocalShiftLedger.weight]
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact Nat.mul_le_mul (Finset.card_le_univ s.val) (Nat.add_le_add F.power_bounded F.rank_bounded)
  have finish (U) : ManuscriptQLocalConditionalGradeTail.low (P U) D K = (phase 1 U).part s :=
    (complete (P U) (degree U) (within.trans (by dsimp [K];omega))).trans (eval U 1)
  change Measurable (fun U=>ManuscriptQLocalConditionalGradeTail.low (P U) D K) at meas
  refine ⟨by simpa only [finish] using meas,?_⟩
  intro r w₀ M mp age later room shift y I
  rw [←same] at pay
  have raised := shift.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀
    (R.family.path.levels.fits.delayed (L.level r)).le (Nat.le_add_right h cap)) mp)
  have physical:=pay r d.cutoff d.period later d.below age room w₀ M mp raised
  have corr:=bill (d.level+1) (Nat.le_succ _) d.below (age.trans later)
    (RG17.atRef L 4 r (d.cutoff,d.period) w₀) y I
  have power : ((K+1:ℕ):ℝ)-1=(K:ℝ):=by push_cast; ring
  rw [power,Real.rpow_natCast] at corr
  have result : ‖∫U,((Poly.toll w s:ℂ)*((raw U).part s-ManuscriptQLocalConditionalGradeTail.low (P U) D K))*
      centered R (Nat.le_succ _) d.below (RG17.atRef L 4 r (d.cutoff,d.period) w₀) y I U ∂μ‖ ≤ ε*g^q*M :=
    corr.trans physical
  simpa only [finish] using result

end YM.Integration.WilsonInvariantActionReportedQMoment
