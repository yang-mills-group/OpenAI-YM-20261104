import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFourSmearedWardReadings
import YM.Integration.WilsonGraphPublishedShapeEstimate

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneIntegratedWardEntryBounds
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

theorem weighted {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    (μ : Measure α) (w f b : α → ℂ) (C : ℝ)
    (hw : Integrable (fun x => ‖w x‖) μ)
    (h : ∀ x ∈ tsupport w, ‖f x - b x‖ ≤ C) :
    ‖∫ x, w x * (f x - b x) ∂μ‖ ≤ (∫ x, ‖w x‖ ∂μ) * C := by
  calc
    _ ≤ ∫ x, ‖w x‖ * C ∂μ := by
      apply norm_integral_le_of_norm_le (hw.mul_const C)
      filter_upwards with x
      rw [norm_mul]
      by_cases hx : w x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_left (h x (subset_tsupport w hx)) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

theorem difference {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    (μ : Measure α) (w f b : α → ℂ) (C : ℝ)
    (hw : Integrable (fun x => ‖w x‖) μ)
    (hf : Integrable (fun x => w x * f x) μ) (hb : Integrable (fun x => w x * b x) μ)
    (h : ∀ x ∈ tsupport w, ‖f x - b x‖ ≤ C) :
    ‖(∫ x, w x * f x ∂μ) - ∫ x, w x * b x ∂μ‖ ≤ (∫ x, ‖w x‖ ∂μ) * C := by
  rw [← integral_sub hf hb]
  simpa only [Pi.sub_apply,mul_sub] using weighted μ w f b C hw h

theorem polynomial {α : Type*} [MeasurableSpace α] (μ : Measure α) (w : α → ℂ)
    {m : ℕ} (t : ℂ) (b : Fin m → α → ℂ) (hb : ∀ k, Integrable (fun x => w x * b k x) μ) :
    (∫ x, w x * ∑ k : Fin m, t^k.val * b k x ∂μ) =
      ∑ k : Fin m, t^k.val * ∫ x, w x * b k x ∂μ := by
  calc
    _ = ∫ x, ∑ k : Fin m, t^k.val * (w x * b k x) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k : Fin m, ∫ x, t^k.val * (w x * b k x) ∂μ :=
      integral_finset_sum _ fun k _ => (hb k).const_mul _
    _ = _ := Finset.sum_congr rfl fun k _ => integral_const_mul _ _

def residual (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d)
    (phase : Option (wardHierarchy V).Character) (r : ℝ) (o : E4) (p : ℕ) (x : _root_.YM.Points n) : ℂ :=
  (wardHierarchy V).correlation phase (ElectedMeasurement.inputs V Z r d v) (sites r o x) -
    ∑ k : Fin (p+1), (ElectedMeasurement.clock V Z r : ℂ)^k.val *
      WilsonGraphStandaloneCorrelation.converted
        (PostedAppointedConversion.filed Z Q.MS Q.matching (FVA2.Teller.logNu 1)) k.val (publicLetters d v) x

def EntryPrice {α : Type*} [MeasurableSpace α] (μ : Measure α) (V : Vision E ξ)
    (Z : WilsonPrescription g.core) (Q : Perspective H Z true) {n : ℕ} (cap p : ℕ)
    (w : α → ℂ) (shape : α → _root_.YM.Points n) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ d : Caps n, (∀ i, d i ≤ cap) →
    ∀ (v : FVA2.GradedFar.Inputs g.core d) (phase : Option (wardHierarchy V).Character) (o : E4),
      ‖∫ x, w x * residual V Z Q d v phase r o p (shape x) ∂μ‖ ≤
        (∫ x, ‖w x‖ ∂μ) * (A * (∏ i, YangMills.Matching.sectorMass (B := B₀) (v i)) *
          |ElectedMeasurement.clock V Z r|^(p+1))

theorem compactEntry {α : Type*} [MeasurableSpace α] [TopologicalSpace α] (μ : Measure α)
    (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (paid : CompactReference Z V Q) {n : ℕ} (cap p : ℕ) (w : α → ℂ) (shape : α → _root_.YM.Points n)
    (K : Set (_root_.YM.Points n)) (hK : IsCompact K) (separated : K ⊆ conf n)
    (inside : ∀ x ∈ tsupport w, shape x ∈ K) (hw : Integrable (fun x => ‖w x‖) μ) :
    EntryPrice μ V Z Q cap p w shape := by
  obtain ⟨A,hA,late⟩ := paid n cap p K hK separated
  refine ⟨A,hA,?_⟩
  filter_upwards [late] with r hr
  intro d hd v phase o
  exact weighted μ w _ _ _ hw fun x hx => hr d hd v phase o (shape x) (inside x hx)

theorem test (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (paid : CompactReference Z V Q) {n : ℕ} (cap p : ℕ) (φ : YangMills.WilsonFamily.SeparatedTest n) :
    EntryPrice volume V Z Q cap p (fun x => φ x) id := by
  apply compactEntry volume V Z Q paid cap p (fun x => φ x) id (tsupport (fun x => φ x))
    φ.hasCompactSupport φ.tsupport_subset (fun _ hx => hx)
  exact φ.continuous.norm.integrable_of_hasCompactSupport φ.hasCompactSupport.norm

theorem derivative (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (paid : CompactReference Z V Q) {n : ℕ} (cap p : ℕ) (φ : YangMills.WilsonFamily.SeparatedTest (n+1))
    (a : YM.Axis) :
    EntryPrice volume V Z Q cap p (YangMills.Ward.firstDerivative a (fun x => φ x)) id := by
  let e : _root_.YM.Points (n+1) := PiLp.single 2 0 (EuclideanSpace.single a 1)
  have hφ : ContDiff ℝ ∞ (fun x => φ x) := φ.contDiff
  have hc : Continuous (fun x => fderiv ℝ (fun y => φ y) x e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  apply compactEntry volume V Z Q paid cap p _ id (tsupport (fun x => φ x))
    φ.hasCompactSupport φ.tsupport_subset
  · exact fun _ hx => tsupport_fderiv_apply_subset ℝ e hx
  · exact hc.norm.integrable_of_hasCompactSupport (φ.hasCompactSupport.fderiv_apply ℝ e).norm

theorem original (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (paid : CompactReference Z V Q) (p : ℕ) (P : Pupils) :
    EntryPrice volume V Z Q 4 p (fun x => P.vacuum x) id ∧
    (∀ row j a, EntryPrice volume V Z Q 4 p
      (YangMills.Ward.firstDerivative a (fun x => P.conservation row j x)) id) ∧
    EntryPrice volume V Z Q 4 p (YangMills.Ward.firstDerivative 0 (fun x => P.translation x)) id :=
  ⟨test V Z Q paid 4 p P.vacuum,fun row j a => derivative V Z Q paid 4 p (P.conservation row j) a,
    derivative V Z Q paid 4 p P.translation 0⟩

end PhysicalMatching.H7StandaloneIntegratedWardEntryBounds
