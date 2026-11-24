import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandalonePhysicalWardOrders
noncomputable section
namespace PhysicalMatching.H7StandaloneInsertedPhysicalWardTests
open YM YM.Answer YM.Answer.ContinuumLimit


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

open YangMills
open _root_.IssuedBridge
open YangMills
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
variable {H : g.core.Simple} {ε : ℝ} {e : YM.Axis} {O : OrderS g.core}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}



open YM.Maxwell.Free YM.Maxwell.Wick YM.XSpace.Normalize
open scoped BigOperators Classical

open PhysicalMatching.H7StandaloneAppointedPublicWardRows
open YangMills.WilsonFamily
open MeasureTheory


open PhysicalMatching.H7StandaloneFourSmearedWardReadings
open YM.Integration.WilsonGraphPublishedShapeEstimate
open YM.Answer.ContinuumLimit.Vision
open scoped Topology
local notation "B₀" => YangMills.maxwellReference g

open PhysicalMatching.H7StandaloneIntegratedWardEntryBounds

open PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients
open YangMills.Matching.CorrelationOnly
open PhysicalMatching.H7StandaloneFiniteWardMatrix


open PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion


open PhysicalMatching.H7StandaloneIntegratedArbitraryWardSeries
open PhysicalMatching.H7StandaloneAppointedWardBalance
open PhysicalMatching.H7StandaloneSmearedConservation
open PhysicalMatching.H7StandaloneArbitraryWardTestReadings


open PhysicalMatching.H7StandaloneWardCoefficientUniqueness


open YangMills.Matching.WardStress

variable {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] [FiniteDimensional ℝ α]
  [MeasureSpace α] [BorelSpace α] [IsLocallyFiniteMeasure (volume : Measure α)]

theorem publicLettersCons {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d)
    (f : (YangMills.maxwellReference g).sector 4) : publicLetters (Fin.cons 4 d) (insertedLabels d v f) =
      Fin.cons ⟨4,f⟩ (publicLetters d v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem publicCoefficientTest (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4)
    (M : YangMills.MSbar.Coefficients B₀) (S : YangMills.Matching.Conversion B₀)
    (read : ∀ (m : ℕ) (e : Caps m) (z : FVA2.GradedFar.Inputs g.core e) (k : ℕ)
      (x : YangMills.Points m), x ∈ conf m → S.correlation M k (publicLetters e z) x =
        groupCoefficient Z Q e z k x)
    {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (k : ℕ)
    (w : α → ℂ) (hw : Continuous w) (hc : HasCompactSupport w)
    (sh : α → YangMills.Points n) (hs : Continuous sh) (clear : ∀ z ∈ tsupport w, sh z ∈ conf n) :
    Integrable (fun z => w z * S.correlation M k (publicLetters d v) (sh z)) ∧
      (∫ z, w z * S.correlation M k (publicLetters d v) (sh z)) =
        ∫ z, w z * groupCoefficient Z Q d v k (sh z) := by
  have h : (fun z => w z * S.correlation M k (publicLetters d v) (sh z)) =
      (fun z => w z * groupCoefficient Z Q d v k (sh z)) := by
    funext z
    by_cases zero : w z = 0
    · simp only [zero,zero_mul]
    · have hz : z ∈ tsupport w := subset_closure (show z ∈ Function.support w from zero)
      rw [read n d v k (sh z) (clear z hz)]
  rw [h]
  exact ⟨coefficientIntegrableOnEveryFiledGrade V Z Q shapes phase o k d v
    w hw hc sh hs clear,rfl⟩

theorem publicInsertedTest (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4)
    (M : YangMills.MSbar.Coefficients B₀) (S : YangMills.Matching.Conversion B₀)
    (P : YangMills.Matching.WardStress.Series B₀)
    (read : ∀ (m : ℕ) (e : Caps m) (z : FVA2.GradedFar.Inputs g.core e) (k : ℕ)
      (x : YangMills.Points m), x ∈ conf m → S.correlation M k (publicLetters e z) x =
        groupCoefficient Z Q e z k x)
    {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (k : ℕ) (a b : YM.Axis)
    (w : α → ℂ) (hw : Continuous w) (hc : HasCompactSupport w)
    (sh : α → YangMills.Points (n+1)) (hs : Continuous sh)
    (clear : ∀ z ∈ tsupport w, sh z ∈ conf (n+1)) :
    Integrable (fun z => w z * YangMills.Matching.WardStress.inserted M S P k a b
      (publicLetters d v) (sh z)) ∧
    (∫ z, w z * YangMills.Matching.WardStress.inserted M S P k a b (publicLetters d v) (sh z)) =
      ∑ j : Fin (k+1), formal Z Q d v w sh (P j.val a b) (k-j.val) := by
  have h : (fun z => w z * YangMills.Matching.WardStress.inserted M S P k a b
        (publicLetters d v) (sh z)) = (fun z => w z * ∑ j : Fin (k+1),
        groupCoefficient Z Q (Fin.cons 4 d) (insertedLabels d v (P j.val a b))
          (k-j.val) (sh z)) := by
    funext z
    by_cases zero : w z = 0
    · simp only [zero,zero_mul]
    · have hz : z ∈ tsupport w := subset_closure (show z ∈ Function.support w from zero)
      unfold YangMills.Matching.WardStress.inserted
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← publicLettersCons d v (P j.val a b)]
      exact read (n+1) (Fin.cons 4 d) (insertedLabels d v (P j.val a b))
        (k-j.val) (sh z) (clear z hz)
  rw [h]
  exact integratedFiledInsertion V Z Q shapes phase o d v w hw hc sh hs clear
    (fun j => P j a b) k

end PhysicalMatching.H7StandaloneInsertedPhysicalWardTests
