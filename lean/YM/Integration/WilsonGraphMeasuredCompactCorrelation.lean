import YM.Integration.WilsonGraphPublicAppointedIncidence
import YM.Integration.WilsonPositionHomogeneousComparison
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNestedFieldColumns

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.Answer.ContinuumLimit

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
universe u
variable {g : YangMills.GaugeGroup} {R : Run g.core}
variable {H : g.core.Simple} {ε : ℝ} {e : Axis} {O : OrderS g.core}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}


open YM.Answer.ContinuumLimit.Vision
open Frames Frames.Cortex Dancer Belfry Belfry.Classroom Belfry.ScaleFits Scale Level GroupS
open SeatsW
open YM.Integration.WilsonGraphStandaloneCorrelation (cutoff within converted)


def publicDegree {n : ℕ} (w : Caps n) : ℕ := Finset.univ.sup w

theorem publicWithin {n : ℕ} (w : Caps n) (i : Fin n) : w i ≤ publicDegree w :=
  Finset.le_sup (Finset.mem_univ i)

def publicLetters {n : ℕ} (w : Caps n) (v : ∀ i : Fin n, Sec g.core (w i)) :
    Fin n → YM.Integration.WilsonGraphStandaloneCorrelation.Label g :=
  fun i => ⟨w i, v i⟩

def publicTruncation (S : YangMills.Matching.Conversion (maxwellReference g))
    {n : ℕ} (a : Fin n → YM.Integration.WilsonGraphStandaloneCorrelation.Label g)
    (x : YangMills.Points n) (b : ℕ) (clock : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (b + 1), (clock : ℂ) ^ j * converted S j a x

theorem publicMixedPolynomial (Z : WilsonPrescription g.core)
    (A : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
    {σ : Prescription (Press.portDeck g.core)} {lamp : Bool} (matched : Main.Match Z H A σ lamp)
    (paid : AllAppointedGraphSums R Z A (Teller.logNu 1))
    {n : ℕ} (w : Caps n) (v : ∀ i : Fin n, Sec g.core (w i)) (x : Stage n) (b : ℕ) (clock : ℝ) :
    polynomial Z A (Teller.logNu 1) (publicDegree w) x
        (toView w (publicDegree w) (publicWithin w) g.core v) b clock =
      publicTruncation (PostedAppointedConversion.filed Z A matched (Teller.logNu 1))
        (publicLetters w v) x.val b clock := by
  unfold YM.Integration.WilsonPositionHomogeneousComparison.polynomial publicTruncation
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun z : ℂ => (clock : ℂ) ^ j * z)
  rw [YM.Integration.WilsonPositionHomogeneousComparison.filed Z A matched]
  have h := publicFiledAt Z A matched paid (publicLetters w v) x j
  rw [Jury.fxt, dif_pos x.property] at h
  have caps : commonCaps (PostedMeasuredCompactCorrelation.leaves (R:=R) w v)
      (publicWithin w) = toView w (publicDegree w) (publicWithin w) g.core v := by
    funext i
    exact PostedNestedFieldColumns.raised (R:=R) w v (publicWithin w) i
  change Measure.outlook Z.scheme Z.criterion (publicDegree w) n x j
      (commonCaps (PostedMeasuredCompactCorrelation.leaves (R:=R) w v) (publicWithin w)) = _ at h
  rwa [caps] at h

def MeasuredMixedCompact (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (A : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
    {σ : Prescription (Press.portDeck g.core)} {lamp : Bool} (matched : Main.Match Z H A σ lamp) : Prop :=
  ∀ {n : ℕ} (b : ℕ) {ι : Type} (l : Filter ι) (r : ι → ℝ), Tendsto r l trail →
    ∀ (U : Set (YM.Points n)), Roi U → ∀ (w : Caps n) (u : ι → ∀ j : Fin n, Sec g.core (w j)),
      (∀ j : Fin n, SeatsW.Salary ℂ l 1 (fun i => u i j)) →
      (∀ a : Bool, ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in l, ∀ (F : Peers V) (x : Stage n), x.val ∈ U →
        ‖Life Z V a (r i) w (u i) x.val F - mote (Lamplight Z a (publicDegree w)) b x.val
          (V.T Z (r i)) (toView w (publicDegree w) (publicWithin w) g.core (u i))‖ ≤
            C * |V.T Z (r i)| ^ (b + 1)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in l, ∀ (F : Peers V) (x : Stage n), x.val ∈ U →
        ‖Life Z V true (r i) w (u i) x.val F -
          publicTruncation (PostedAppointedConversion.filed Z A matched (Teller.logNu 1))
            (publicLetters w (u i)) x.val b (V.T Z (r i))‖ ≤ C * |V.T Z (r i)| ^ (b + 1)

theorem publicMixedCompact (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (A : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
    {σ : Prescription (Press.portDeck g.core)} {lamp : Bool} (matched : Main.Match Z H A σ lamp)
    (standalone : Vision.StandaloneCorrelation V Z A)
    (paid : AllAppointedGraphSums R Z A (Teller.logNu 1)) : MeasuredMixedCompact V Z A matched := by
  intro n b ι l r tend U room w u wages
  obtain ⟨arms, C, pos, bound⟩ := standalone.mixedCompact b l r tend U room (Teller.logNu 1)
    w (publicWithin w) u wages
  refine ⟨arms, C, pos, ?_⟩
  filter_upwards [bound] with i hi
  intro F x hx
  rw [← publicMixedPolynomial Z A matched paid w (u i) x b (V.T Z (r i))]
  exact hi F x hx

theorem publicMeasuredOnGroup (hg : g.IsSimple) (V : Vision E ξ) (lamp : Bool) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z lamp, Q.MS = A ∧ Vision.StandaloneCorrelation V Z A ∧
      (cT Z < 0 ∧ ∀ r : ℝ, cT Z * V.T Z r = (Signal V Z r).re) ∧
      MeasuredMixedCompact V Z Q.MS Q.matching := by
  dsimp only
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  obtain ⟨Q, hQ, hV, paid⟩ := separatedGraphSumOnGroupFiledDatum (R:=E.paths) hg V lamp
  refine ⟨Q, hQ, hV, ⟨hV.negative, hV.measured⟩, ?_⟩
  apply publicMixedCompact (R:=E.paths) V Z Q.MS Q.matching
  · rw [hQ]
    exact hV
  · rw [hQ]
    exact paid

end YM.Answer.ContinuumLimit
end
