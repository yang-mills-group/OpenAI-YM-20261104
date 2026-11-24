import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneIntegratedTriangularTestKernel
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion
import YM.MS.Book.Triang

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneIntegratedArbitraryWardSeries
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

theorem integralAtCap {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [FiniteDimensional ℝ α] [MeasureSpace α] [BorelSpace α]
    [IsLocallyFiniteMeasure (volume : Measure α)] (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4) (p : ℕ) {n : ℕ}
    (cap : ℕ) (d : Caps n) (within : ∀ i, d i ≤ cap) (v : FVA2.GradedFar.Inputs g.core d)
    (w : α → ℂ) (hw : Continuous w) (hc : HasCompactSupport w) (sh : α → YangMills.Points n)
    (hs : Continuous sh) (clear : ∀ z ∈ tsupport w, sh z ∈ conf n) :
    RowPrice (ElectedMeasurement.clock V Z) p
      (fun r => ∫ z, w z * (wardHierarchy V).correlation phase (ElectedMeasurement.inputs V Z r d v) (sites r o (sh z)))
      (fun k => ∫ z, w z * groupCoefficient Z Q d v k (sh z)) := by
  let K := sh '' tsupport w
  have hK : IsCompact K := hc.image hs
  have sep : K ⊆ conf n := by rintro _ ⟨z,hz,rfl⟩; exact clear z hz
  have crops := filedCrops V Z Q shapes cap d within v phase o
  have ib (k : ℕ) : Integrable (fun z => w z * groupCoefficient Z Q d v k (sh z)) :=
    weightedIntegrable w hw hc sh hs _ (coefficientContinuousOn (ElectedMeasurement.positive V Z Q) crops K hK sep k)
  obtain ⟨A,hA,priced⟩ := compactEntry volume V Z Q (referenceCompact Z V Q shapes) cap p w sh K hK sep
    (fun z hz => ⟨z,hz,rfl⟩) (hw.norm.integrable_of_hasCompactSupport hc.norm)
  obtain ⟨B,hB,smooth⟩ := crops p K hK sep
  let mass := ∏ i, YangMills.Matching.sectorMass (B := B₀) (v i)
  let C := (∫ z, ‖w z‖) * (A * mass)
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  filter_upwards [priced,smooth] with r hr hsr
  have ia := weightedIntegrable w hw hc sh hs
    (fun x => (wardHierarchy V).correlation phase (ElectedMeasurement.inputs V Z r d v) (sites r o x))
    (fun x hx => (hsr x hx).1.continuousAt.continuousWithinAt)
  have h := hr d within v phase o
  rw [integralResidual volume V Z Q d v phase r o p w sh ia (fun k => ib k.val)] at h
  calc
    _ ≤ (∫ z, ‖w z‖) * (A * mass * |ElectedMeasurement.clock V Z r|^(p+1)) := h
    _ = C * |ElectedMeasurement.clock V Z r|^(p+1) := by simp only [C,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (abs_nonneg _) _)


theorem integralOnEveryFiledGrade {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [FiniteDimensional ℝ α] [MeasureSpace α] [BorelSpace α]
    [IsLocallyFiniteMeasure (volume : Measure α)] (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4) (p : ℕ) {n : ℕ}
    (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d)
    (w : α → ℂ) (hw : Continuous w) (hc : HasCompactSupport w) (sh : α → YangMills.Points n)
    (hs : Continuous sh) (clear : ∀ z ∈ tsupport w, sh z ∈ conf n) :
    RowPrice (ElectedMeasurement.clock V Z) p
      (fun r => ∫ z, w z * (wardHierarchy V).correlation phase (ElectedMeasurement.inputs V Z r d v) (sites r o (sh z)))
      (fun k => ∫ z, w z * groupCoefficient Z Q d v k (sh z)) := by
  classical
  let cap := max 4 (Finset.univ.sup d)
  have within (i : Fin n) : d i ≤ cap :=
    (Finset.le_sup (f := d) (Finset.mem_univ i)).trans (le_max_right _ _)
  exact integralAtCap V Z Q shapes phase o p cap d within v w hw hc sh hs clear

private theorem rangeIic (p : ℕ) : Finset.range (p+1) = Finset.Iic p := by
  ext i
  simp [Nat.lt_succ_iff]

private theorem finIic (p : ℕ) (f : ℕ → ℂ) :
    (∑ i : Fin (p+1), f i.val) = ∑ i ∈ Finset.Iic p, f i := by
  rw [Fin.sum_univ_eq_sum_range, rangeIic]

theorem triangularCrop (t : ℂ) (p : ℕ) (c : ℕ → ℕ → ℂ) :
    (∑ j : Fin (p+1), t^j.val * ∑ i : Fin (p-j.val+1), t^i.val * c j.val i.val) =
      ∑ k : Fin (p+1), t^k.val * ∑ j : Fin (k.val+1), c j.val (k.val-j.val) := by
  exact PhysicalMatching.H7StandaloneIntegratedTriangularTestKernel.triangularCrop t p c

theorem integratedInsertion (clock : ℝ → ℝ) (a : ℝ → ℂ) (slots : ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℂ)
    (moving : ∀ p, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖a r - ∑ j : Fin (p+1), (clock r : ℂ)^j.val * slots j.val r‖ ≤ K*|clock r|^(p+1))
    (fixed : ∀ j q, RowPrice clock q (slots j) (c j)) (p : ℕ) :
    RowPrice clock p a (fun k => ∑ j : Fin (k+1), c j.val (k-j.val)) := by
  exact PhysicalMatching.H7StandaloneIntegratedTriangularTestKernel.integratedInsertion clock a slots c moving fixed p

theorem coordinateTail (clock : ℝ → ℝ) (u : ℝ → Fin 4 → ℂ) (U : ℕ → Fin 4 → ℂ)
    (columns : Fin 4 → ℝ → ℂ)
    (price : ∀ p, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i,
      ‖u r i - ∑ j : Fin (p+1), (clock r : ℂ)^j.val * U j.val i‖ ≤ K * |clock r|^(p+1))
    (bounded : ∀ i, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ‖columns i r‖ ≤ D)
    (p : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖(∑ i, u r i * columns i r) - ∑ j : Fin (p+1), (clock r : ℂ)^j.val *
        ∑ i, U j.val i * columns i r‖ ≤ K * |clock r|^(p+1) := by
  exact PhysicalMatching.H7StandaloneIntegratedTriangularTestKernel.coordinateTail clock u U columns price bounded p

theorem pricedColumnBound {clock : ℝ → ℝ} (small : ∀ᶠ r : ℝ in 𝓝[>] 0, |clock r| ≤ 1)
    {a : ℝ → ℂ} {c : ℕ → ℂ} (h : RowPrice clock 0 a c) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ‖a r‖ ≤ D := by
  exact PhysicalMatching.H7StandaloneIntegratedTriangularTestKernel.pricedColumnBound small h

end PhysicalMatching.H7StandaloneIntegratedArbitraryWardSeries

