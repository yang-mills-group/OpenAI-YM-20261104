import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFourSmearedWardReadings
import YM.Integration.WilsonGraphAppointedPublicMeasurement
import YM.Integration.WilsonGraphMeasuredCompactCorrelation
import YangMills.WilsonProof.NativeSupport.WardBridge
import YangMills.WilsonProof.NativeSupport.MaxwellBridge
import YM.XSpace.Twins
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Stress

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneAppointedWardBalance
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
open PhysicalMatching.H7StandaloneFourSmearedWardReadings
open YangMills.WilsonFamily

def degrees (V : Vision E ξ) {n : ℕ} (d : ℕ) (q : Fin n → (wardHierarchy V).Tag) : Fin (n+1) → ℕ :=
  Fin.cons d (fun i => (q i).1)

def tailFields (V : Vision E ξ) {n : ℕ} (d : ℕ) (q : Fin n → (wardHierarchy V).Tag) :
    ∀ i : Fin (n+1), V.pupil.S.Field (degrees V d q i) :=
  Fin.cases (motive := fun i => V.pupil.S.Field (degrees V d q i)) 0 (fun j => (q j).2)

def firstSlot (V : Vision E ξ) (s : Option (wardHierarchy V).Character) {n : ℕ} (d : ℕ)
    (q : Fin n → (wardHierarchy V).Tag) (x : YangMills.Points (n+1)) :
    (wardHierarchy V).Field d →ₗ[ℂ] ℂ :=
  (V.pupil.S.classMoment (spectator V.pupil.last s) (degrees V d q) x).toLinearMap (tailFields V d q) 0

theorem firstSlot_eq (V : Vision E ξ) (s : Option (wardHierarchy V).Character) {n : ℕ} (d : ℕ)
    (q : Fin n → (wardHierarchy V).Tag) (x : YangMills.Points (n+1)) (w : (wardHierarchy V).Field d) :
    (wardHierarchy V).correlation s (Fin.cons ⟨d,w⟩ q) x = firstSlot V s d q x w := by
  classical
  have he : Fin.cons (α := fun _ : Fin (n+1) => (wardHierarchy V).Tag) ⟨d,w⟩ q =
      (fun i => ⟨degrees V d q i, Function.update (tailFields V d q) 0 w i⟩) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [degrees, Function.update] <;> rfl
    · simp [degrees, tailFields, Function.update] <;> rfl
  rw [he]
  rfl

theorem scaledFieldDivergence (V : Vision E ξ) (t : ℂ) (b : YM.Axis) :
    (∑ a : YM.Axis, (PhysicalMatching.H7StandaloneAppointedPublicWardRows.original V).derivative 4 a
      (t • (wardHierarchy V).stress a b)) = 0 := by
  rw [show (∑ a : YM.Axis, (PhysicalMatching.H7StandaloneAppointedPublicWardRows.original V).derivative 4 a
      (t • (wardHierarchy V).stress a b)) = t • ∑ a : YM.Axis,
      (PhysicalMatching.H7StandaloneAppointedPublicWardRows.original V).derivative 4 a ((wardHierarchy V).stress a b) by
    simp only [map_smul, Finset.smul_sum]]
  rw [(PhysicalMatching.H7StandaloneAppointedPublicWardRows.original V).divergence b, smul_zero]

theorem separatedConservation (V : Vision E ξ) (s : Option (wardHierarchy V).Character)
    {n : ℕ} (q : Fin n → (wardHierarchy V).Tag) (x : YangMills.Points (n+1))
    (hx : x ∈ YangMills.WilsonFamily.separated (n+1)) (t : ℂ) (b : YM.Axis) :
    (∑ a : YM.Axis, YangMills.Ward.firstDerivative a
      ((wardHierarchy V).correlation s (Fin.cons ⟨4,t • (wardHierarchy V).stress a b⟩ q)) x) = 0 := by
  let W := PhysicalMatching.H7StandaloneAppointedPublicWardRows.original V
  calc
    _ = ∑ a : YM.Axis, (wardHierarchy V).correlation s
        (Fin.cons ⟨5,W.derivative 4 a (t • (wardHierarchy V).stress a b)⟩ q) x := by
      apply Finset.sum_congr rfl
      intro a _
      exact (W.derivativeInsertion s 4 a (t • (wardHierarchy V).stress a b) x hx q).symm
    _ = firstSlot V s 5 q x (∑ a : YM.Axis, W.derivative 4 a (t • (wardHierarchy V).stress a b)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact firstSlot_eq V s 5 q x _
    _ = 0 := by
      rw [scaledFieldDivergence V t b, map_zero]

theorem atBookedSites (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (s : Option (wardHierarchy V).Character) {n : ℕ} (q : Fin n → (wardHierarchy V).Tag)
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) (x : YangMills.Points (n+1))
    (hx : x ∈ YM.conf (n+1)) (b : YM.Axis) :
    (∑ a : YM.Axis, YangMills.Ward.firstDerivative a ((wardHierarchy V).correlation s
      (Fin.cons ⟨4, YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4
        (measuredStress V Z r a b)⟩ q)) (sites r o x)) = 0 := by
  simp only [frameReconstruction]
  exact separatedConservation V s q (sites r o x) (YM.Answer.ContinuumLimit.ElectedMeasurement.centerSeparated hr o x hx) (r^4 : ℂ) b

end PhysicalMatching.H7StandaloneAppointedWardBalance

