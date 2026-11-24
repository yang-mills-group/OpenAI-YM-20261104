import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandalonePublicInsertedWardIntegrals
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


open YangMills YangMills.Matching
open PhysicalMatching.H7StandaloneArbitraryWardTestReadings

theorem gradeLabelTuple {n : ℕ} (v : Fin n → YangMills.Matching.Label B₀) :
    publicLetters (fun i => (v i).1) (fun i => (v i).2) = v := by
  funext i
  change (⟨(v i).1,(v i).2⟩ : YangMills.Matching.Label B₀) = v i
  cases v i
  rfl

theorem determinedOnFiledCoordinates (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4)
    (M : YangMills.MSbar.Coefficients B₀) (S : YangMills.Matching.Conversion B₀)
    (P : YangMills.Matching.WardStress.Series B₀)
    (u : ℝ → Fin 4 → ℂ) (U : ℕ → Fin 4 → ℂ)
    (coordinates : ∀ k a b, P k a b = ∑ i, U k i • columns H a b i)
    (ground : U 0 = ![0,0,0,1])
    (symmetry : ∀ k a b, P k a b = P k b a)
    (axes : ∀ (k : ℕ) (σ : Equiv.Perm YM.Axis) (sign : YM.Axis → ℝ)
      (L : YangMills.Spacetime ≃ₗᵢ[ℝ] YangMills.Spacetime),
      (∀ a, sign a = 1 ∨ sign a = -1) →
      (∀ a, L (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1) →
      ∀ a b, RelatedByAxes B₀ σ sign L (P k a b).val
        (((sign a * sign b : ℝ) : ℂ) • (P k (σ a) (σ b)).val))
    (read : ∀ (m : ℕ) (e : Caps m) (z : FVA2.GradedFar.Inputs g.core e) (k : ℕ)
      (x : YangMills.Points m), x ∈ conf m → S.correlation M k (publicLetters e z) x =
        groupCoefficient Z Q e z k x)
    (real : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ a b, measuredStress V Z r a b = ∑ i, u r i • columns H a b i)
    (small : ∀ᶠ r in 𝓝[>] (0:ℝ), |ElectedMeasurement.clock V Z r| ≤ 1)
    (shrinks : Tendsto (ElectedMeasurement.clock V Z) (𝓝[>] 0) (𝓝 0))
    (fourth : ∀ m : ℕ, Tendsto (fun r : ℝ => r^4 / (ElectedMeasurement.clock V Z r)^m)
      (𝓝[>] 0) (𝓝 0))
    (paid : ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i,
      ‖u r i - ∑ j : Fin (p+1), (ElectedMeasurement.clock V Z r : ℂ)^j.val * U j.val i‖
        ≤ C * |ElectedMeasurement.clock V Z r|^(p+1)) : YangMills.Matching.WardStress.Determined M S P := by
  classical
  refine
    { leading := ?_
      symmetric := symmetry
      signedAxes := axes
      vacuum := ?_
      conservation := ?_
      translation := ?_ }
  · intro a b
    rw [coordinates,ground]
    simp [Fin.sum_univ_succ,PhysicalMatching.H7StandaloneAppointedPublicWardRows.columns]
  · intro k a b φ
    let d : Caps 0 := fun i => Fin.elim0 i
    let v : FVA2.GradedFar.Inputs g.core d := fun i => Fin.elim0 i
    have empty : publicLetters d v = (fun i : Fin 0 => Fin.elim0 i) :=
      funext fun i => Fin.elim0 i
    have h := publicInsertedTest V Z Q shapes phase o M S P read d v k a b (fun z => φ z)
      φ.continuous φ.hasCompactSupport id continuous_id (fun x hx => φ.tsupport_subset hx)
    have v0 := vacuumAtEveryOrder V Z Q shapes phase o φ a b u U
      (real.mono fun r h => h a b) small shrinks fourth paid k
    refine ⟨by simpa only [empty,id_eq] using h.1,?_⟩
    rw [← empty]
    have hv : (∑ j : Fin (k+1), formal Z Q d v (fun z => φ z) id (P j.val a b) (k-j.val)) = 0 := by
      simpa only [coordinates,d,v] using v0
    simpa only [id_eq] using h.2.trans hv
  · intro n k b tags φ
    let d : Caps n := fun i => (tags i).1
    let v : FVA2.GradedFar.Inputs g.core d := fun i => (tags i).2
    have tuple : publicLetters d v = tags := gradeLabelTuple tags
    let w a := YangMills.Ward.firstDerivative a (fun y => φ y)
    have reg a := derivativeWeight φ a
    have test a := publicInsertedTest V Z Q shapes phase o M S P read d v k a b (w a)
      (reg a).1 (reg a).2.1 (fun x : YangMills.Points (n+1) => x) continuous_id (fun x hx => (reg a).2.2 hx)
    have van := conservationAtEveryOrder (V := V) (Z := Z) (Q := Q) (shapes := shapes)
      (phase := phase) (o := o) (d := d) (v := v) (φ := φ) (b := b) (u := u) (U := U)
      (real := real) (small := small) (shrinks := shrinks) (paid := paid) k
    refine ⟨fun a => by simpa only [w,tuple,id_eq] using (test a).1,?_⟩
    calc
      (∑ a : YM.Axis, ∫ x, w a x * YangMills.Matching.WardStress.inserted M S P k a b tags x) =
          ∑ a : YM.Axis, ∑ j : Fin (k+1), formal Z Q d v (w a) (fun x : YangMills.Points (n+1) => x) (P j.val a b) (k-j.val) := by
        apply Finset.sum_congr rfl
        intro a _
        simpa only [tuple,id_eq] using (test a).2
      _ = 0 := by simpa only [w,coordinates] using van
  · intro n k b tags φ χ window
    let d : Caps (n+1) := fun i => (tags i).1
    let v : FVA2.GradedFar.Inputs g.core d := fun i => (tags i).2
    have tuple : publicLetters d v = tags := gradeLabelTuple tags
    let W : PhysicalMatching.H7StandaloneArbitraryWardTestReadings.Shell n := ⟨φ,χ,window⟩
    let w := PhysicalMatching.H7StandaloneArbitraryWardTestReadings.weight W
    let sh (z : YangMills.Spacetime × YangMills.Points (n+1)) := YangMills.Ward.prepend z.1 z.2
    have hsh : Continuous sh := by exact PhysicalMatching.H7StandaloneInsertedPhysicalWardTests.arbitraryPrependContinuous _
    have test a := publicInsertedTest V Z Q shapes phase o M S P read d v k a b (w a)
      (PhysicalMatching.H7StandaloneArbitraryWardTestReadings.smoothWeight W a)
      (PhysicalMatching.H7StandaloneArbitraryWardTestReadings.compact W a) sh hsh
      (fun z hz => PhysicalMatching.H7StandaloneArbitraryWardTestReadings.separated W a hz)
    let wt := YangMills.Ward.firstDerivative b (fun y => φ y)
    have reg := derivativeWeight φ b
    have rhs := publicCoefficientTest V Z Q shapes phase o M S read d v k wt reg.1 reg.2.1
      id continuous_id (fun x hx => reg.2.2 hx)
    have law := translationAtEveryOrder V Z Q shapes phase o d v b W u U real small shrinks paid k
    have each (a : YM.Axis) : Integrable (YangMills.Matching.WardStress.fluxIntegrand M S P k
          tags φ χ a b) ∧ (∫ z, YangMills.Matching.WardStress.fluxIntegrand M S P k
          tags φ χ a b z) = ∑ j : Fin (k+1), formal Z Q d v (w a) sh (P j.val a b) (k-j.val) := by
      have hfun : YangMills.Matching.WardStress.fluxIntegrand M S P k tags φ χ a b =
          (fun z : YangMills.Spacetime × YangMills.Points (n+1) =>
            w a z * YangMills.Matching.WardStress.inserted M S P k a b (publicLetters d v) (sh z)) := by
        funext z
        rw [tuple]
        rfl
      rw [hfun]
      have pvol : (volume : Measure (YangMills.Spacetime × YangMills.Points (n+1))) =
          (volume : Measure YangMills.Spacetime).prod (volume : Measure (YangMills.Points (n+1))) := rfl
      simpa only [pvol] using test a
    refine ⟨by simpa only [tuple,id_eq,wt] using rhs.1,fun a => (each a).1,?_⟩
    calc
      -(∑ a : YM.Axis, ∫ z, YangMills.Matching.WardStress.fluxIntegrand M S P k tags φ χ a b z) =
          -(∑ a : YM.Axis, ∑ j : Fin (k+1), formal Z Q d v (w a) sh (P j.val a b) (k-j.val)) := by
        congr 1
        exact Finset.sum_congr rfl fun a _ => (each a).2
      _ = -(∫ x, wt x * groupCoefficient Z Q d v k x) := by
        simpa only [w,sh,wt,W,coordinates] using law
      _ = -(∫ x, wt x * S.correlation M k tags x) := by
        congr 1
        simpa only [tuple,id_eq] using rhs.2.symm

end PhysicalMatching.H7StandaloneInsertedPhysicalWardTests
