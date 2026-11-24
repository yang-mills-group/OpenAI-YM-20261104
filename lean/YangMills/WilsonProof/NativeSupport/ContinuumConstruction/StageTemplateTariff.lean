import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.OriginalStageCostPublication
import YM.WilsonCoeffUV.Step.Stencils
import YM.WilsonCoeffUV.Step.Branches
import YM.WilsonCoeffUV.Step.Log
import YM.RG.Block
import YM.RG.Patch
import YM.PCalc.Loop
import YM.XSpace.Bare

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Answer.ContinuumLimit.StageTariff
open YM YM.Integration
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open Push.PriceCompiler ThroughLaunch WilsonLimitConstruction.FundedCompanySelection
open WilsonFundedWindowMenu WilsonWindowJointPurchase Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank YM.Planned.PrimaryIntegral295
open Laurent Exterior Bloch Matrix Stationary Blue Next.Free FreeResolvent Tree Gauge Metric
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G : Gauge}

def referenceSide (P : Patch) : Side := ⟨2 * (P.radius + P.L.val + 2) + 1, by omega⟩

def referenceStep (K : KernelChoices) (P : Patch) :
    StepData (referenceSide P) (referenceSide P * P.L) := ⟨P, K, rfl⟩

theorem referenceLarge (P : Patch) :
    2 * (P.radius + P.L.val + 1) < (referenceSide P).val := by
  change 2 * (P.radius + P.L.val + 1) < 2 * (P.radius + P.L.val + 2) + 1
  omega

def localPenalty (G : Gauge) {c f : Side} (S : StepData c f) (i : Edge (Site c))
    (x : Lawn (WilsonCoeffUV.Joint G f c)) : ℝ :=
  S.kernel.penalty * G.price (mantle (rightArm x) i *
    (S.prediction (mantle (leftArm x)) (tac S) i)⁻¹)

theorem localPenaltySmooth (G : Gauge) {c f : Side} (S : StepData c f)
    (h : S.patch.Branches S.kernel G) (i : Edge (Site c)) : Green (localPenalty G S i) := by
  unfold Green localPenalty
  refine ContDiffAt.mul contDiffAt_const ?_
  have he : Green fun x : Lawn (WilsonCoeffUV.Joint G f c)=> (cloth G f).symm (leftArm x) := by
    simp_rw [←left_hit]; apply (cloth G f).symm.contDiff.contDiffAt.comp 0 (board _)
  let M (x:Lawn (WilsonCoeffUV.Joint G f c)):= (cloth G f).symm (leftArm x)
  have hm : M 0=0:= by unfold M; rw [show leftArm (0:Lawn (WilsonCoeffUV.Joint G f c))=0 from rfl,map_zero]
  have ht : Green (fun x : Lawn (WilsonCoeffUV.Joint G f c)=> G.mat (S.prediction (mantle (leftArm x)) (tac S) i)) := by
    have hh : ContDiffAt ℝ ω (fun v=> G.mat (S.prediction (represent v) (tac S) i)) (M 0) := by rw [hm]; exact Push.prediction_cont S h i _
    exact hh.comp (f:=M) 0 he
  apply Work.F03.price_smooth (A:=fun x: Lawn (WilsonCoeffUV.Joint G f c)=> mantle (rightArm x) i* (S.prediction (mantle (leftArm x)) (tac S) i)⁻¹)
  simp only [G.mat_mul,G.mat_inv];
  apply ContDiffAt.mul ?_ ((starL ℝ).contDiff.contDiffAt.comp 0 ht)
  simp_rw [←right_hit]; exact (mantle_green _).contDiffAt.comp 0 (board _)

theorem jointLocal (G : Gauge) {c f : Side} (S : StepData c f) (x : Lawn (WilsonCoeffUV.Joint G f c)) :
    jointPen G S x = ∑ i, localPenalty G S i x := by
  unfold jointPen localPenalty noiseTaylor
  rw [Finset.mul_sum]

def shellMoment (w : ℝ) (r : ℕ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ r * (Real.exp (-w)) ^ n

theorem shellMomentSummable {w : ℝ} (positive : 0 < w) (r : ℕ) :
    Summable fun n : ℕ => (n : ℝ) ^ r * (Real.exp (-w)) ^ n := by
  apply summable_pow_mul_geometric_of_norm_lt_one
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos positive)

def convertedStripFare (w B : ℝ) (r : ℕ) : ℝ :=
  |B| * 2 ^ (r+4) * ((1 - Real.exp (-w))⁻¹ + shellMoment w (r+4))

def extraPre (G : Gauge) (K : KernelChoices) (j t : ℕ) (o : Orders) : List ℝ :=
  if hj : 4 ≤ j then
    if ht : 4 ≤ t then
      let k := K.penalty
      let hs := forms_tail k K.penalty_pos t ht
      let cs := Bank.crank_fee G k K.penalty_pos hj ht
      let w := (schedule_flat K G j t hj ht).choose
      let degree := o.1 + o.2.1 + o.2.2.1 + o.2.2.2
      [1, convertedStripFare hs.choose hs.choose_spec.choose degree,
        convertedStripFare cs.choose cs.choose_spec.choose degree, convertedStripFare w 1 degree]
    else [1]
  else [1]

def extraPost {s : Sheet G} (D : Rolls s) (P : Patch) (_t : ℕ) (o : Orders) : List ℝ :=
  let S := referenceStep s.kernel P
  let r := o.2.1+2
  let q := o.2.2.1
  let m := o.2.2.2
  let localTaylor := ∑ i, ‖iteratedFDeriv ℝ r (localPenalty G S i) 0‖
  let joinedTaylor := ‖iteratedFDeriv ℝ r (jointPen G S) 0‖
  let haar := ‖iteratedFDeriv ℝ o.1 (chart G).J 0‖
  let haarLog := ‖iteratedFDeriv ℝ r (fun x => Real.log ((chart G).J x)) 0‖
  let slots := (Fintype.card (WilsonCoeffUV.Joint G (referenceSide P * P.L) (referenceSide P)) : ℝ)
  let distance := (1+(P.radius+P.L.val+1 : ℕ) : ℝ)
  let weight := (1+slots)^r * distance^(r*(m+q))
  [1, (D.L P.J).val, (referenceSide P).val, slots, distance, weight,
    localTaylor, joinedTaylor, haar, haarLog,
    weight*localTaylor, weight*joinedTaylor, weight*haar, weight*haarLog]

def paper (G : Gauge) : Additional G where
  pre := extraPre G
  post := extraPost

def paperCosts (G : Gauge) : PhysicalMatching.H7JointWeakBookPrices.Costs G where
  pre := fun s j => max 1 ((costs (paper G)).pre s j)
  post := fun D j => max 1 ((costs (paper G)).post D j)
  pre_nonneg := fun _ _ => zero_le_one.trans (le_max_left _ _)
  post_nonneg := fun _ _ => zero_le_one.trans (le_max_left _ _)
  raised := fun _ _ => rfl

theorem paperPre (s : Sheet G) {j : ℕ} {x : ℝ} (h : x ∈ preMenu (paper G) s.kernel j) :
    |x| ≤ (paperCosts G).pre s j := (preCovered _ _ _ h).trans (le_max_right _ _)

theorem paperPost {s : Sheet G} (D : Rolls s) {j : ℕ} {x : ℝ}
    (h : x ∈ postMenu (paper G) D j) : |x| ≤ (paperCosts G).post D j :=
  (postCovered _ _ _ h).trans (le_max_right _ _)

end YM.Answer.ContinuumLimit.StageTariff

namespace YM.Answer.ContinuumLimit.PreElectedPublication
open Filter Function Set YangMills YangMills.Wilson
open YM YM.Integration YM.Answer.ContinuumLimit YM.Extraction YM.FullVolume
open Climb Lattice Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open Election SignedWilsonExpansion.Museum
open _root_.IssuedBridge.PhysicalPeriodNodes
open scoped Classical Topology

variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ} {e : YM.Axis}
  {O : YM.Integration.Election.OrderS g.core}

open Lattice RG MeasureTheory Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.High MS.Native MS.Land MS.Fleet MS.Tide MS.Book PhysMS PhysMS.Frame Next.UVStress Order Spin OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale.Level FVA2.Scale SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Asymptotics WilsonPositionHomogeneousComparison
open PowerSeries XSpace.Cirrus Entree Future
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Scale OPE OPE.Orbits
open SignedWilsonExpansion SignedWilsonExpansion.Kane SignedWilsonExpansion.StageG Camera SignedWilsonExpansion.Kane.Tilted Next.UVStress XSpace.Cirrus
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book PowerSeries Asymptotics
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open scoped BigOperators Classical ContDiff Topology
open YangMills YangMills.Wilson
open _root_.IssuedBridge
open YangMills YangMills.Wilson
open YM YM.Integration YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open WilsonOneFrameMixedMaxwell WilsonPositionHomogeneousFrame
open Climb Lattice RG PhysMS Trace.Pilot Next.Extract PhysicalNext.Repeat.Legato RG17 XSpace XSpace.Normalize FVA2 FVA2.Register
open FixedFields
open Function Filter Set
open scoped Topology BigOperators Classical
open MS MS.Land MS.Fleet FVA2.Scale WilsonViewerReportingGrid WilsonThermometerWeakMeasuredSeries
open WilsonViewerGridPins WilsonViewerAlignedResidual WilsonViewerElectedHierarchy
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonLimitConstruction
open YM.FVA2.Scale YM.MS YM.MS.Fleet YM.MS.Land YangMills.Matching
open YangMills.Matching
open YM.Answer.ContinuumLimit.Vision
open Frames Frames.Cortex Dancer Belfry Belfry.Classroom Belfry.ScaleFits Scale Level GroupS
open SeatsW
open YM.Integration.WilsonGraphStandaloneCorrelation (cutoff within converted)

theorem originalPaper (hg : g.IsSimple) (a : YM.Axis) (H : g.core.Simple)
    {ε : ℝ} (positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core) :
    StagePricedBeforeAll.{u} hg H ε a O (StageTariff.paperCosts g.core) := by
  let c := StageTariff.paperCosts g.core
  obtain ⟨E, earned, rest⟩ := measuredOriginal.{u} hg a H positive O c
  exact ⟨E, StageTariff.onRun c E.paths earned, earned, rest⟩

end YM.Answer.ContinuumLimit.PreElectedPublication
