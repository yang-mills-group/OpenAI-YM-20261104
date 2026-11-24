import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneIntegratedArbitraryWardSeries
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneArbitraryWardTestReadings

set_option autoImplicit false
set_option maxHeartbeats 1400000
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

def insertedLabels {G : YM.Gauge} {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs G d)
    (u : Sec G 4) : FVA2.GradedFar.Inputs G (Fin.cons 4 d) := by
  let grades : Fin (n+1) → ℕ := Fin.cons 4 d
  have firstGrade : grades 0 = 4 := rfl
  have laterGrade (i : Fin n) : grades i.succ = d i := rfl
  intro i
  change Sec G (grades i)
  refine Fin.cases (motive := fun k => Sec G (grades k)) ?_ (fun j => ?_) i
  · rw [firstGrade]
    exact u
  · rw [laterGrade]
    exact v j

theorem insertedInputs (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ)
    {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (u : (YangMills.maxwellReference g).sector 4) :
    ElectedMeasurement.inputs V Z r (Fin.cons 4 d) (insertedLabels d v u) =
      Fin.cons ⟨4, ElectedMeasurement.frame V Z r 4 u⟩ (ElectedMeasurement.inputs V Z r d v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

variable {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] [FiniteDimensional ℝ α]
  [MeasureSpace α] [BorelSpace α] [IsLocallyFiniteMeasure (volume : Measure α)]

def occupied (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (phase : Option (wardHierarchy V).Character) (o : E4) {n : ℕ}
    (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (w : α → ℂ)
    (sh : α → YangMills.Points (n+1)) (u : (YangMills.maxwellReference g).sector 4) (r : ℝ) : ℂ :=
  ∫ z, w z * marked V phase r o (ElectedMeasurement.frame V Z r 4 u)
    (ElectedMeasurement.inputs V Z r d v) (sh z)

def formal (Z : WilsonPrescription g.core) (Q : Perspective H Z true) {n : ℕ}
    (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (w : α → ℂ)
    (sh : α → YangMills.Points (n+1)) (u : (YangMills.maxwellReference g).sector 4) (k : ℕ) : ℂ :=
  ∫ z, w z * groupCoefficient Z Q (Fin.cons 4 d) (insertedLabels d v u) k (sh z)

theorem fixed (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character) (o : E4)
    {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (w : α → ℂ)
    (hw : Continuous w) (hc : HasCompactSupport w) (sh : α → YangMills.Points (n+1))
    (hs : Continuous sh) (clear : ∀ z ∈ tsupport w, sh z ∈ conf (n+1)) (u : (YangMills.maxwellReference g).sector 4) (p : ℕ) :
    RowPrice (ElectedMeasurement.clock V Z) p (occupied V Z phase o d v w sh u)
      (formal Z Q d v w sh u) := by
  have paid := integralOnEveryFiledGrade V Z Q shapes phase o p (Fin.cons 4 d)
    (insertedLabels d v u) w hw hc sh hs clear
  unfold occupied formal
  simp only [PhysicalMatching.H7StandaloneFourSmearedWardReadings.marked]
  simp only [insertedInputs] at paid
  exact paid

theorem fieldIntegral (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (phase : Option (wardHierarchy V).Character) (o : E4)
    {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (w : α → ℂ)
    (hw : Continuous w) (hc : HasCompactSupport w) (sh : α → YangMills.Points (n+1))
    (hs : Continuous sh) (clear : ∀ z ∈ tsupport w, sh z ∈ conf (n+1))
    {r : ℝ} (hr : 0 < r) :
    ∃ L : (YangMills.maxwellReference g).sector 4 →ₗ[ℂ] ℂ, ∀ u, L u = occupied V Z phase o d v w sh u r := by
  let q := ElectedMeasurement.inputs V Z r d v
  let ev (z : α) := (firstSlot V phase 4 q (sites r o (sh z))).comp (ElectedMeasurement.frame V Z r 4).toLinearMap
  have reads (u : (YangMills.maxwellReference g).sector 4) (z : α) :
      marked V phase r o (ElectedMeasurement.frame V Z r 4 u) q (sh z) = ev z u :=
    firstSlot_eq V phase 4 q (sites r o (sh z)) _
  have good (u : (YangMills.maxwellReference g).sector 4) : Integrable (fun z => w z * ev z u) := by
    simp_rw [← reads u]
    apply weightedIntegrable w hw hc sh hs
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hx
    exact (shapedSmooth V phase (Fin.cons ⟨4, ElectedMeasurement.frame V Z r 4 u⟩ q)
      r hr o (sh z) (clear z hz)).continuousAt.continuousWithinAt
  refine ⟨{ toFun := fun u => ∫ z, w z * ev z u
            map_add' := ?_
            map_smul' := ?_ },?_⟩
  · intro u u'
    simp only [map_add, mul_add]
    exact integral_add (good u) (good u')
  · intro c u
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    simpa only [mul_left_comm] using integral_const_mul c (fun z => w z * ev z u)
  · intro u
    change (∫ z, w z * ev z u) = ∫ z, w z * marked V phase r o (ElectedMeasurement.frame V Z r 4 u) q (sh z)
    simp_rw [reads u]

theorem insertedPrice (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character) (o : E4)
    {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (w : α → ℂ)
    (hw : Continuous w) (hc : HasCompactSupport w) (sh : α → YangMills.Points (n+1))
    (hs : Continuous sh) (clear : ∀ z ∈ tsupport w, sh z ∈ conf (n+1))
    (a b : YM.Axis) (u : ℝ → Fin 4 → ℂ) (U : ℕ → Fin 4 → ℂ)
    (real : ∀ᶠ r : ℝ in 𝓝[>] 0, measuredStress V Z r a b = ∑ i, u r i • columns H a b i)
    (small : ∀ᶠ r : ℝ in 𝓝[>] 0, |ElectedMeasurement.clock V Z r| ≤ 1)
    (paid : ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i,
      ‖u r i - ∑ j : Fin (p+1), (ElectedMeasurement.clock V Z r : ℂ)^j.val * U j.val i‖
        ≤ C * |ElectedMeasurement.clock V Z r|^(p+1)) (p : ℕ) :
    RowPrice (ElectedMeasurement.clock V Z) p
      (fun r => occupied V Z phase o d v w sh (measuredStress V Z r a b) r)
      (fun k => ∑ j : Fin (k+1), formal Z Q d v w sh
        (∑ i, U j.val i • columns H a b i) (k-j.val)) := by
  let col (i : Fin 4) := occupied V Z phase o d v w sh (columns H a b i)
  let pol (k : ℕ) := ∑ i, U k i • columns H a b i
  have bound (i : Fin 4) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ‖col i r‖ ≤ C :=
    pricedColumnBound small (fixed V Z Q shapes phase o d v w hw hc sh hs clear (columns H a b i) 0)
  apply integratedInsertion (ElectedMeasurement.clock V Z) _
    (fun j => occupied V Z phase o d v w sh (pol j)) (fun j => formal Z Q d v w sh (pol j))
  · intro h
    obtain ⟨C,hC,hpriced⟩ := coordinateTail (ElectedMeasurement.clock V Z) u U col paid bound h
    refine ⟨C,hC,?_⟩
    have pos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
    filter_upwards [pos,real,hpriced] with r hr hspan hrow
    obtain ⟨L,hL⟩ := fieldIntegral V Z phase o d v w hw hc sh hs clear hr
    have observed (c : Fin 4 → ℂ) :
        occupied V Z phase o d v w sh (∑ i, c i • columns H a b i) r = ∑ i, c i * col i r := by
      rw [← hL, map_sum]
      simp only [map_smul, smul_eq_mul]
      simp only [hL, col]
    simpa only [hspan, pol, observed] using hrow
  · intro j h
    exact fixed V Z Q shapes phase o d v w hw hc sh hs clear (pol j) h

end PhysicalMatching.H7StandaloneInsertedPhysicalWardTests
