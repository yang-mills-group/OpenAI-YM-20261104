import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneAppointedPublicWardRows
import YM.Integration.WilsonGraphAppointedPublicMeasurement
import YM.Integration.WilsonGraphMeasuredCompactCorrelation
import YangMills.WilsonProof.NativeSupport.WardBridge
import YangMills.WilsonProof.NativeSupport.MaxwellBridge
import YM.XSpace.Twins
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Stress

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneFourSmearedWardReadings
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

structure Pupils where
  vacuum : YangMills.WilsonFamily.SeparatedTest 1
  conservation : Fin 2 → Fin 2 → YangMills.WilsonFamily.SeparatedTest 2
  translation : YangMills.WilsonFamily.SeparatedTest 2
  cutoff : YangMills.Spacetime → ℝ
  window : ∀ x ∈ tsupport (fun y => translation y), YangMills.Ward.Window x cutoff

def sites {n : ℕ} (r : ℝ) (o : YangMills.Spacetime) (x : YangMills.Points n) :
    YangMills.Points n := WithLp.toLp 2 fun i => o + r • x i

def probes (hg : g.core.Simple) : Fin 2 → (YangMills.maxwellReference g).sector 4 :=
  ![square hg 5, square hg 0]

def probeTag (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ) (i : Fin 2) :
    (wardHierarchy V).Tag :=
  ⟨4, YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4 (probes H i)⟩

def marked (V : Vision E ξ) (s : Option (wardHierarchy V).Character) (r : ℝ)
    (o : YangMills.Spacetime) {n : ℕ} (w : (wardHierarchy V).Field 4)
    (q : Fin n → (wardHierarchy V).Tag) (x : YangMills.Points (n+1)) : ℂ :=
  (wardHierarchy V).correlation s (Fin.cons ⟨4,w⟩ q) (sites r o x)

def vacuum (V : Vision E ξ) (s : Option (wardHierarchy V).Character) (r : ℝ)
    (o : YangMills.Spacetime) (P : Pupils) (W : YM.Axis → YM.Axis → (wardHierarchy V).Field 4) : ℂ :=
  ∫ x : YangMills.Points 1, P.vacuum x * marked V s r o (W 0 0) (fun i : Fin 0 => Fin.elim0 i) x

def conservation (V : Vision E ξ) (Z : WilsonPrescription g.core) (s : Option (wardHierarchy V).Character)
    (r : ℝ) (o : YangMills.Spacetime) (P : Pupils)
    (W : YM.Axis → YM.Axis → (wardHierarchy V).Field 4) (row : Fin 2) : ℂ :=
  ∑ j : Fin 2, ∑ a : YM.Axis, ∫ x : YangMills.Points 2,
    YangMills.Ward.firstDerivative a (fun y => P.conservation row j y) x *
      marked V s r o (W a 0) (fun _ : Fin 1 => probeTag V Z r j) x

def flux (V : Vision E ξ) (Z : WilsonPrescription g.core) (s : Option (wardHierarchy V).Character)
    (r : ℝ) (o : YangMills.Spacetime) (P : Pupils) (W : YM.Axis → YM.Axis → (wardHierarchy V).Field 4) : ℂ :=
  -(∑ a : YM.Axis, ∫ z : YangMills.Spacetime × YangMills.Points 2,
    P.translation z.2 * ((YangMills.Maxwell.partialD a P.cutoff z.1 : ℝ) : ℂ) *
      marked V s r o (W a 0) (fun _ : Fin 2 => probeTag V Z r 0) (YangMills.Ward.prepend z.1 z.2))

def readings (V : Vision E ξ) (Z : WilsonPrescription g.core) (s : Option (wardHierarchy V).Character)
    (r : ℝ) (o : YangMills.Spacetime) (P : Pupils) (W : YM.Axis → YM.Axis → (wardHierarchy V).Field 4) :
    Fin 4 → ℂ :=
  ![vacuum V s r o P W, conservation V Z s r o P W 0,
    conservation V Z s r o P W 1, flux V Z s r o P W]

def matrix (V : Vision E ξ) (Z : WilsonPrescription g.core) (s : Option (wardHierarchy V).Character)
    (r : ℝ) (o : YangMills.Spacetime) (P : Pupils) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i k => readings V Z s r o P (fun a b => physicalColumns V Z r a b k) i

def rightSide (V : Vision E ξ) (Z : WilsonPrescription g.core) (s : Option (wardHierarchy V).Character)
    (r : ℝ) (o : YangMills.Spacetime) (P : Pupils) : Fin 4 → ℂ :=
  ![0,0,0,-(∫ x : YangMills.Points 2, YangMills.Ward.firstDerivative 0 (fun y => P.translation y) x *
    (wardHierarchy V).correlation s (fun _ : Fin 2 => probeTag V Z r 0) (sites r o x))]

theorem probeNames (hg : g.core.Simple) :
    (probes hg 0).val = label g.core 5 5 ∧ (probes hg 1).val = label g.core 0 0 := ⟨rfl,rfl⟩

theorem filedColumns (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (s : Option (wardHierarchy V).Character) (r : ℝ) (o : YangMills.Spacetime) (P : Pupils) (k : Fin 4) :
    (fun i => matrix V Z s r o P i k) =
      readings V Z s r o P (fun a b => YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4 (columns H a b k)) := rfl

theorem physicalStress (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (s : Option (wardHierarchy V).Character) (r : ℝ) (o : YangMills.Spacetime) (P : Pupils) :
    readings V Z s r o P (fun a b => YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4 (measuredStress V Z r a b)) =
      readings V Z s r o P (fun a b => (r ^ 4 : ℂ) • V.pupil.last.sector.energy a b) := by
  simp only [frameReconstruction]

end PhysicalMatching.H7StandaloneFourSmearedWardReadings

