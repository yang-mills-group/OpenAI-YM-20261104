import YM.Integration.WilsonGraphAppointedPublicMeasurement
import YM.Integration.WilsonGraphMeasuredCompactCorrelation
import YangMills.WilsonProof.NativeSupport.WardBridge
import YangMills.WilsonProof.NativeSupport.MaxwellBridge
import YM.XSpace.Twins
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Stress

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneAppointedPublicWardRows
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
def original (V : Vision E ξ) :
    (YangMills.hierarchy V.pupil.last V.pupil.P).StressWardLaws :=
  YangMills.publicWards V.pupil.last V.pupil.P

theorem charges (V : Vision E ξ) (v : Viewers V.pupil.last) :
    Table.StressLaws (spectator V.pupil.last v) V.pupil.last.sector.energy
      V.pupil.last.sector.derivatives.deriv V.pupil.last.sector.turns.lie := by
  cases v with
  | none => exact V.pupil.last.phase.transport.charges
  | some i => exact V.pupil.last.phase.phase.flux i

theorem energy (V : Vision E ξ) (a b : YM.Axis) :
    (YangMills.hierarchy V.pupil.last V.pupil.P).stress a b =
      V.pupil.last.sector.energy a b := rfl

theorem unitAtFour (V : Vision E ξ) :
    (YangMills.hierarchy V.pupil.last V.pupil.P).unitAtFour = V.pupil.S.unit 4 := rfl

def unitLabel (hg : g.core.Simple) : (YangMills.maxwellReference g).sector 4 :=
  ⟨1, ((low_span (shellSector g.core 4) hg).mp le_rfl).1⟩

def square (hg : g.core.Simple) (i : Index) : (YangMills.maxwellReference g).sector 4 :=
  ⟨label g.core i i, ((low_span (shellSector g.core 4) hg).mp le_rfl).2 i i le_rfl⟩

theorem squareProbes (hg : g.core.Simple) :
    (square hg 5).val = label g.core 5 5 ∧
    (square hg 0).val = label g.core 0 0 ∧
    left 5 = 2 ∧ right 5 = 3 ∧ left 0 = 0 ∧ right 0 = 1 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def diagonalEnergy (g : YangMills.GaugeGroup) (b : YM.Axis) :
    (YangMills.maxwellReference g).sector 4 := by
  refine ⟨sheetEnergy (G:=g.core) b b, sector.mpr ⟨?_,?_⟩⟩
  · apply Submodule.sum_mem
    intro i _
    have he : MvPolynomial.IsWeightedHomogeneous scaleW (phi (G:=g.core) b b i i) 4 := by
      unfold phi
      apply MvPolynomial.IsWeightedHomogeneous.sum
      intro c _
      exact (symbol_hom (omegaLeg (G:=g.core) c b i) (fun j => j+2)).mul
        (symbol_hom (omegaLeg (G:=g.core) c b i) (fun j => j+2))
    rw [lowerCap,MvPolynomial.mem_restrictSupport_iff]
    intro p hp
    change degree p ≤ 4
    exact (he (MvPolynomial.mem_support_iff.mp hp)).le
  · intro u
    simp only [sheetEnergy,map_sum,shade_phi]

def columns (hg : g.core.Simple) (a b : YM.Axis) : Fin 4 → (YangMills.maxwellReference g).sector 4 :=
  ![if a = b then unitLabel hg else 0, if a = b then diagonalEnergy g b else 0,
    if a = b then ∑ i : Index, square hg i else 0, (YangMills.maxwellReference g).stress a b]

def physicalColumns (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ) (a b : YM.Axis) :
    Fin 4 → (YangMills.hierarchy V.pupil.last V.pupil.P).Field 4 :=
  fun i => YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4 (columns H a b i)

def measuredStress (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ) (a b : YM.Axis) :
    (YangMills.maxwellReference g).sector 4 :=
  (YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4).symm ((r ^ 4 : ℂ) • (YangMills.hierarchy V.pupil.last V.pupil.P).stress a b)

theorem frameReconstruction (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ) (a b : YM.Axis) :
    YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4 (measuredStress V Z r a b) =
      (r ^ 4 : ℂ) • V.pupil.last.sector.energy a b := by
  exact (YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4).apply_symm_apply _


abbrev wardHierarchy (V : Vision E ξ) := YangMills.hierarchy V.pupil.last V.pupil.P

theorem signedTranslation (V : Vision E ξ) (s : Option (wardHierarchy V).Character)
    {n d : ℕ} (x : YangMills.Points (n+1)) (hx : x ∈ YangMills.WilsonFamily.separated (n+1))
    (v : (wardHierarchy V).Field d) (q : Fin n → (wardHierarchy V).Tag)
    (χ : YangMills.Spacetime → ℝ) (window : YangMills.Ward.Window x χ) (b : YangMills.Axis) :
    (wardHierarchy V).translationFlux s x v q χ b =
      YangMills.Ward.firstDerivative b ((wardHierarchy V).correlation s (Fin.cons ⟨d,v⟩ q)) x :=
  (original V).translation s x hx v q χ window b

theorem signedRotation (V : Vision E ξ) (s : Option (wardHierarchy V).Character)
    {n d : ℕ} (x : YangMills.Points (n+1)) (hx : x ∈ YangMills.WilsonFamily.separated (n+1))
    (v : (wardHierarchy V).Field d) (q : Fin n → (wardHierarchy V).Tag)
    (χ : YangMills.Spacetime → ℝ) (window : YangMills.Ward.Window x χ) (A : YangMills.Ward.Generator) :
    (wardHierarchy V).rotationFlux s x v q χ A =
      (wardHierarchy V).correlation s (Fin.cons ⟨d,(original V).generator d A v⟩ q) x :=
  (original V).rotation s x hx v q χ window A

end PhysicalMatching.H7StandaloneAppointedPublicWardRows

