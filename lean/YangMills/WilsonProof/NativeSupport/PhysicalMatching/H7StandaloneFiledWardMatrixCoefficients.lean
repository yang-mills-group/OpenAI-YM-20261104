import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneIntegratedWardEntryBounds
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneTranslationTestSupport
import YM.Integration.WilsonGraphPublishedShapeEstimate

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients
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

def groupCoefficient (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (k : ℕ) (x : YangMills.Points n) : ℂ :=
  WilsonGraphStandaloneCorrelation.converted
    (PostedAppointedConversion.filed Z Q.MS Q.matching (FVA2.Teller.logNu 1)) k (publicLetters d v) x

def markedLabels (hg : g.core.Simple) (a b : YM.Axis) (m : Fin 4) {n : ℕ} (t : Fin n → Fin 2) :
    FVA2.GradedFar.Inputs g.core (fun _ : Fin (n+1) => 4) :=
  Fin.cons (columns hg a b m) (fun i => probes hg (t i))

def groupMarked (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (k : ℕ) (a b : YM.Axis) (m : Fin 4) {n : ℕ} (t : Fin n → Fin 2) (x : YangMills.Points (n+1)) : ℂ :=
  groupCoefficient Z Q (fun _ => 4) (markedLabels H a b m t) k x

def vacuumEntry (Z : WilsonPrescription g.core) (Q : Perspective H Z true) (P : Pupils)
    (k : ℕ) (m : Fin 4) : ℂ :=
  ∫ x : YangMills.Points 1, P.vacuum x * groupMarked Z Q k 0 0 m (fun i : Fin 0 => Fin.elim0 i) x

def conservationEntry (Z : WilsonPrescription g.core) (Q : Perspective H Z true) (P : Pupils)
    (k : ℕ) (row : Fin 2) (m : Fin 4) : ℂ :=
  ∑ j : Fin 2, ∑ a : YM.Axis, ∫ x : YangMills.Points 2,
    YangMills.Ward.firstDerivative a (fun y => P.conservation row j y) x *
      groupMarked Z Q k a 0 m (fun _ : Fin 1 => j) x

def fluxEntry (Z : WilsonPrescription g.core) (Q : Perspective H Z true) (P : Pupils)
    (k : ℕ) (m : Fin 4) : ℂ :=
  -(∑ a : YM.Axis, ∫ z : YangMills.Spacetime × YangMills.Points 2,
    H7StandaloneTranslationTestSupport.weight P a z *
      groupMarked Z Q k a 0 m (fun _ : Fin 2 => 0) (YangMills.Ward.prepend z.1 z.2))

def matrixCoefficients (Z : WilsonPrescription g.core) (Q : Perspective H Z true) (P : Pupils)
    (k : ℕ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i m => ![vacuumEntry Z Q P k m,conservationEntry Z Q P k 0 m,
    conservationEntry Z Q P k 1 m,fluxEntry Z Q P k m] i

def rhsCoefficients (Z : WilsonPrescription g.core) (Q : Perspective H Z true) (P : Pupils)
    (k : ℕ) : Fin 4 → ℂ :=
  ![0,0,0,-(∫ x : YangMills.Points 2, YangMills.Ward.firstDerivative 0 (fun y => P.translation y) x *
    groupCoefficient Z Q (fun _ : Fin 2 => 4) (fun _ => probes H 0) k x)]

theorem markedInputs (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ)
    (a b : YM.Axis) (m : Fin 4) {n : ℕ} (t : Fin n → Fin 2) :
    ElectedMeasurement.inputs V Z r (fun _ => 4) (markedLabels H a b m t) =
      Fin.cons ⟨4,physicalColumns V Z r a b m⟩ (fun i => probeTag V Z r (t i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem markedResidual (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (s : Option (wardHierarchy V).Character) (r : ℝ) (o : E4) (p : ℕ)
    (a b : YM.Axis) (m : Fin 4) {n : ℕ} (t : Fin n → Fin 2) (x : YangMills.Points (n+1)) :
    H7StandaloneIntegratedWardEntryBounds.residual V Z Q (fun _ => 4) (markedLabels H a b m t) s r o p x =
      marked V s r o (physicalColumns V Z r a b m) (fun i => probeTag V Z r (t i)) x -
      ∑ k : Fin (p+1), (ElectedMeasurement.clock V Z r : ℂ)^k.val * groupMarked Z Q k.val a b m t x := by
  unfold H7StandaloneIntegratedWardEntryBounds.residual
  rw [markedInputs]
  rfl

theorem prependContinuous : Continuous (fun z : YangMills.Spacetime × YangMills.Points 2 => YangMills.Ward.prepend z.1 z.2) := by
  unfold YangMills.Ward.prepend
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => YangMills.Spacetime)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => YangMills.Spacetime) j).comp continuous_snd

theorem shellPrice (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (paid : CompactReference Z V Q) (P : Pupils) (p : ℕ) (a : YM.Axis) :
    EntryPrice volume V Z Q 4 p (H7StandaloneTranslationTestSupport.weight P a)
      (fun z => YangMills.Ward.prepend z.1 z.2) := by
  let w := H7StandaloneTranslationTestSupport.weight P a
  let sh := fun z : YangMills.Spacetime × YangMills.Points 2 => YangMills.Ward.prepend z.1 z.2
  apply compactEntry volume V Z Q paid 4 p w sh (sh '' tsupport w)
  · exact (H7StandaloneTranslationTestSupport.compact P a).image prependContinuous
  · rintro _ ⟨z,hz,rfl⟩
    exact H7StandaloneTranslationTestSupport.separated P a hz
  · exact fun z hz => ⟨z,hz,rfl⟩
  · exact (H7StandaloneTranslationTestSupport.smoothWeight P a).norm.integrable_of_hasCompactSupport
      (H7StandaloneTranslationTestSupport.compact P a).norm

theorem integralResidual {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d)
    (s : Option (wardHierarchy V).Character) (r : ℝ) (o : E4) (p : ℕ)
    (w : α → ℂ) (sh : α → YangMills.Points n)
    (hf : Integrable (fun x => w x * (wardHierarchy V).correlation s
      (ElectedMeasurement.inputs V Z r d v) (sites r o (sh x))) μ)
    (hb : ∀ k : Fin (p+1), Integrable (fun x => w x * groupCoefficient Z Q d v k.val (sh x)) μ) :
    (∫ x, w x * H7StandaloneIntegratedWardEntryBounds.residual V Z Q d v s r o p (sh x) ∂μ) =
      (∫ x, w x * (wardHierarchy V).correlation s (ElectedMeasurement.inputs V Z r d v) (sites r o (sh x)) ∂μ) -
      ∑ k : Fin (p+1), (ElectedMeasurement.clock V Z r : ℂ)^k.val *
        ∫ x, w x * groupCoefficient Z Q d v k.val (sh x) ∂μ := by
  let t : ℂ := ElectedMeasurement.clock V Z r
  let b := fun k : Fin (p+1) => fun x => groupCoefficient Z Q d v k.val (sh x)
  have hm (x : α) : w x * (∑ k, t^k.val * b k x) = ∑ k, t^k.val * (w x * b k x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hs : Integrable (fun x => w x * ∑ k, t^k.val * b k x) μ := by
    simp_rw [hm]
    exact integrable_finsetSum _ fun k _ => (hb k).const_mul _
  rw [← PhysicalMatching.H7StandaloneIntegratedWardEntryBounds.polynomial μ w t b hb,← integral_sub hf hs]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Pi.sub_apply,H7StandaloneIntegratedWardEntryBounds.residual,groupCoefficient,b,t,mul_sub]

theorem original (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (paid : CompactReference Z V Q) (p : ℕ) (P : Pupils) :
    EntryPrice volume V Z Q 4 p (fun x => P.vacuum x) id ∧
    (∀ row j a, EntryPrice volume V Z Q 4 p
      (YangMills.Ward.firstDerivative a (fun x => P.conservation row j x)) id) ∧
    (∀ a, EntryPrice volume V Z Q 4 p (H7StandaloneTranslationTestSupport.weight P a)
      (fun z => YangMills.Ward.prepend z.1 z.2)) ∧
    EntryPrice volume V Z Q 4 p (YangMills.Ward.firstDerivative 0 (fun x => P.translation x)) id := by
  obtain ⟨h0,h12,hb⟩ := PhysicalMatching.H7StandaloneIntegratedWardEntryBounds.original V Z Q paid p P
  exact ⟨h0,h12,shellPrice V Z Q paid P p,hb⟩

end PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients
