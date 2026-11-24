import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.PreElectedMeasuredPublication
import YM.WilsonCoeffUV.Flat.Width
import YM.WilsonCoeffUV.Flat.Hessian
import YM.WilsonCoeffUV.Vacuum.Gain.DiagonalRows
import YM.WilsonCoeffUV.Wick.Fourier
import YM.Planned.PRIMARY_INTEGRAL_295.RollFilm
import YM.Planned.PRIMARY_INTEGRAL_295.East

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
open scoped Classical
variable {G : Gauge}

abbrev Orders := ℕ × ℕ × ℕ × ℕ

def requests (j : ℕ) : List Orders :=
  (List.range (j+1)).flatMap fun d =>
    (List.range (j+1)).flatMap fun k =>
      (List.range (j-2+1)).flatMap fun q =>
        (List.range (j+1)).map fun m => (d,k,q,m)

theorem requested {j d k q m : ℕ} (hd : d ≤ j) (hk : k ≤ j) (hq : q ≤ j-2) (hm : m ≤ j) :
    (d,k,q,m) ∈ requests j := by
  apply List.mem_flatMap.mpr
  refine ⟨d,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨k,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_range.mpr (by omega),?_⟩
  exact List.mem_map.mpr ⟨m,List.mem_range.mpr (by omega),rfl⟩

structure Additional (G : Gauge) where
  pre : KernelChoices → ℕ → ℕ → Orders → List ℝ
  post : {s : Sheet G} → Rolls s → Patch → ℕ → Orders → List ℝ

def base (G : Gauge) : Additional G where
  pre := fun _ _ _ _ => []
  post := fun _ _ _ _ => []

def ceiling : List ℝ → ℝ
  | [] => 0
  | x :: xs => max |x| (ceiling xs)

theorem ceiling_nonneg (xs : List ℝ) : 0 ≤ ceiling xs := by
  cases xs with
  | nil => rfl
  | cons x xs => exact (abs_nonneg x).trans (le_max_left _ _)

theorem covered {xs : List ℝ} {x : ℝ} (hx : x ∈ xs) : |x| ≤ ceiling xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

def preAt (a : Additional G) (K : KernelChoices) (j t : ℕ) : List ℝ :=
  if hj : 4 ≤ j then
    if ht : 4 ≤ t then
      let k := K.penalty
      let gap := (vacuum_positive k K.penalty_pos ht).choose
      let hessian := forms_tail k K.penalty_pos t ht
      let crank := Bank.crank_fee G k K.penalty_pos hj ht
      let wick := (Bank.Carp.starFumes k ht).choose
      let width := (schedule_flat K G j t hj ht).choose
      let degrees := List.ofFn fun d : Fin (j+1) =>
        let hd : d.val ≤ j := Nat.le_of_lt_succ d.isLt
        let film := (Carrier.deliver (E := ℝ) k K.penalty_pos hj ht d.val hd).choose
        let east := (PPX.toll (localSection G d.val) (Next.Foundations.sound G d.val)
          k K.penalty_pos ht (valuation G d.val) hj hd (π := 2) (by norm_num)).choose
        [film,east]
      [gap,gap⁻¹,hessian.choose,hessian.choose⁻¹,hessian.choose_spec.choose,
        crank.choose,crank.choose⁻¹,crank.choose_spec.choose,wick,width,width⁻¹] ++
        degrees.flatten ++ (requests j).flatMap (a.pre K j t)
    else []
  else []

def postAt (a : Additional G) {s : Sheet G} (D : Rolls s) (j t : ℕ) : List ℝ :=
  if hj : 4 ≤ j then
    if ht : 4 ≤ t then
      let P : Patch := ⟨D.L j,j,hj,(D.large j).size,(D.large j).odd⟩
      let witness := schedule_flat s.kernel G j t hj ht
      let bill := (witness.choose_spec.2 P rfl (s.has P)).choose
      [witness.choose,witness.choose⁻¹,bill] ++
        (requests j).flatMap (a.post D P t)
    else []
  else []

def preMenu (a : Additional G) (K : KernelChoices) (j : ℕ) : List ℝ :=
  [j-1,j].flatMap (preAt a K j)

def postMenu (a : Additional G) {s : Sheet G} (D : Rolls s) (j : ℕ) : List ℝ :=
  ((D.L j).val : ℝ) :: [j-1,j].flatMap (postAt a D j)

def costs (a : Additional G) : PhysicalMatching.H7JointWeakBookPrices.Costs G where
  pre := fun s j => ceiling (preMenu a s.kernel j)
  post := fun D j => ceiling (postMenu a D j)
  pre_nonneg := fun _ _ => ceiling_nonneg _
  post_nonneg := fun _ _ => ceiling_nonneg _
  raised := fun _ _ => rfl

theorem preCovered (a : Additional G) (s : Sheet G) (j : ℕ) {x : ℝ}
    (present : x ∈ preMenu a s.kernel j) : |x| ≤ (costs a).pre s j := covered present

theorem postCovered (a : Additional G) {s : Sheet G} (D : Rolls s) (j : ℕ) {x : ℝ}
    (present : x ∈ postMenu a D j) : |x| ≤ (costs a).post D j := covered present

def ActualBills (c : PhysicalMatching.H7JointWeakBookPrices.Costs G) (R : Run G) : Prop :=
  R.metals.O = chart G ∧
  (∀ j, max (Ticket.floors G R.metals.p.kernel id j)
    (Nat.ceil ((2+c.pre R.metals.p j)^(j^2))) ≤ R.metals.p.floorL j) ∧
  (∀ j, max (Ticket.voucher R.rolls id R.metals.O j)
    (Real.exp (Real.exp (2+c.post R.rolls j))) ≤ R.alloy.delay.betaEntry j)

theorem onRun (c : PhysicalMatching.H7JointWeakBookPrices.Costs G) (R : Run G)
    (earned : PhysicalMatching.H7OriginalWeakBookBudget.prediction c R.kit) : ActualBills c R :=
  PhysicalMatching.H7OriginalWeakBookBudget.amounts c R earned
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

def StagePricedBeforeAll (hg : g.IsSimple) (H : g.core.Simple) (ε : ℝ) (a : YM.Axis)
    (O : YM.Integration.Election.OrderS g.core) (c : PhysicalMatching.H7JointWeakBookPrices.Costs g.core) : Prop :=
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let A := YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core
  ∃ E : Construction.{u} H ε a O, StageTariff.ActualBills c E.paths ∧ PhysicalMatching.H7OriginalWeakBookBudget.prediction c E.paths.kit ∧
    ∃ row : Row E, Fixed E row ∧ Clusters E row ∧
    ∀ (cohort : Ultrafilter (ℕ × ℕ) → Prop)
      (_issued : ∀ (ξ : YM.Extraction.Order) (l : Ultrafilter (ℕ × ℕ)),
        (l : Filter (ℕ × ℕ)) ≤ ξ.fuse → cohort l),
    ∃ pick : (ξ : YM.Extraction.Order) → Vision E ξ,
      (∀ ξ, Retained E cohort ξ (pick ξ)) ∧ (∀ ξ, Reads E row (pick ξ)) ∧
      (∀ (ξ : YM.Extraction.Order) (lamp : Bool), ∃ Q : Perspective H Z lamp, Q.MS = A ∧
        Vision.StandaloneCorrelation (pick ξ) Z A ∧ SourceOnlyGraphSum.EveryCoefficient Z A
          (YM.FVA2.Teller.logNu 1) ∧
        (cT Z < 0 ∧ ∀ r : ℝ, cT Z * (pick ξ).T Z r = (Signal (pick ξ) Z r).re) ∧
        MeasuredMixedCompact (pick ξ) Z Q.MS Q.matching) ∧ Receipts hg E pick

theorem stagePurchased (hg : g.IsSimple) (a : YM.Axis) (H : g.core.Simple) {ε : ℝ}
    (positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core)
    (additional : StageTariff.Additional g.core) :
    StagePricedBeforeAll.{u} hg H ε a O (StageTariff.costs additional) := by
  let c := StageTariff.costs additional
  obtain ⟨E,earned,rest⟩ := measuredOriginal.{u} hg a H positive O c
  exact ⟨E,StageTariff.onRun c E.paths earned,earned,rest⟩

theorem stageOriginal (hg : g.IsSimple) (a : YM.Axis) (H : g.core.Simple) {ε : ℝ}
    (positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core) :
    StagePricedBeforeAll.{u} hg H ε a O (StageTariff.costs (StageTariff.base g.core)) :=
  stagePurchased hg a H positive O (StageTariff.base g.core)
end YM.Answer.ContinuumLimit.PreElectedPublication
end
