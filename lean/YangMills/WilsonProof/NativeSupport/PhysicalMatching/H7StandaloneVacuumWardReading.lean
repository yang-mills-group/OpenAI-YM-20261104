import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneAppointedWardBalance
import YM.Integration.WilsonGraphAppointedPublicMeasurement
import YM.Integration.WilsonGraphMeasuredCompactCorrelation
import YangMills.WilsonProof.NativeSupport.WardBridge
import YangMills.WilsonProof.NativeSupport.MaxwellBridge
import YM.XSpace.Twins
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Stress

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneVacuumWardReading
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
open PhysicalMatching.H7StandaloneAppointedWardBalance

def emptyTail (V : Vision E ξ) : Fin 0 → (wardHierarchy V).Tag := fun i => Fin.elim0 i

def atOrigin (V : Vision E ξ) (s : Option (wardHierarchy V).Character)
    (w : (wardHierarchy V).Field 4) : ℂ :=
  (wardHierarchy V).correlation s (Fin.cons ⟨4,w⟩ (emptyTail V)) (0 : YangMills.Points 1)

theorem atEveryHome (V : Vision E ξ) (s : Option (wardHierarchy V).Character)
    (r : ℝ) (o : YangMills.Spacetime) (x : YangMills.Points 1) (w : (wardHierarchy V).Field 4) :
    marked V s r o w (emptyTail V) x = atOrigin V s w := by
  let q := Fin.cons (α := fun _ : Fin 1 => (wardHierarchy V).Tag) ⟨4,w⟩ (emptyTail V)
  let c := (sites r o x) 0
  have e : sites r o x = YM.Points.across c (0 : YangMills.Points 1) := by
    ext1 i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [YM.Points.across_coord]
    change c = 0 + c
    simp
  have he : (0 : YangMills.Points 1) ∈ YM.conf 1 := by
    intro i j hij
    exact Subsingleton.elim _ _
  change V.pupil.S.useAt (spectator V.pupil.last s) (sites r o x) q =
    V.pupil.S.useAt (spectator V.pupil.last s) 0 q
  rw [e]
  exact (spectate V.pupil.last s).translations 1 (0 : YangMills.Points 1) he c
    (fun i => ⟨(q i).1,V.pupil.S.representative (q i).1 (q i).2⟩)

theorem originLinear (V : Vision E ξ) (s : Option (wardHierarchy V).Character)
    (z : ℂ) (w : (wardHierarchy V).Field 4) : atOrigin V s (z • w) = z * atOrigin V s w := by
  unfold atOrigin
  rw [firstSlot_eq,firstSlot_eq,map_smul]
  rfl

theorem original (V : Vision E ξ) (s : Option (wardHierarchy V).Character) (r : ℝ)
    (o : YangMills.Spacetime) (P : Pupils) :
    vacuum V s r o P (fun a b => (r^4 : ℂ) • (wardHierarchy V).stress a b) =
      (r^4 : ℂ) * ((∫ x : YangMills.Points 1, P.vacuum x) *
        atOrigin V s ((wardHierarchy V).stress 0 0)) := by
  change (∫ x : YangMills.Points 1, P.vacuum x *
    marked V s r o ((r^4 : ℂ) • (wardHierarchy V).stress 0 0) (emptyTail V) x) = _
  simp_rw [atEveryHome,originLinear]
  rw [integral_mul_const]
  ring

theorem bounded (V : Vision E ξ) (s : Option (wardHierarchy V).Character) (P : Pupils) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (o : YangMills.Spacetime),
      ‖vacuum V s r o P (fun a b => (r^4 : ℂ) • (wardHierarchy V).stress a b)‖ ≤ C * |r|^4 := by
  refine ⟨‖(∫ x : YangMills.Points 1, P.vacuum x) * atOrigin V s ((wardHierarchy V).stress 0 0)‖,norm_nonneg _,?_⟩
  intro r o
  rw [original,norm_mul]
  simp [norm_pow,mul_comm]

end PhysicalMatching.H7StandaloneVacuumWardReading

