import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.MatchGraphSum
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ElectedPrescription
import YM.FVA2.Teller.Mass

set_option autoImplicit false
noncomputable section
namespace YM.Answer.ContinuumLimit
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
universe u
variable {G:Gauge}{H:G.Simple}{ε:ℝ}{e:Axis}{O:OrderS G}{E:Construction.{u} H ε e O}
variable {ξ:Extraction.Order} {V:Vision E ξ} {Z:WilsonPrescription G}{dial:Bool} {Q:Perspective H Z dial}

namespace SourceOnlyGraphSum
variable {g : YangMills.GaugeGroup} {Hg : g.core.Simple} {Og : OrderS g.core}
variable {Eg : Construction.{u} Hg ε e Og}
theorem groupFiled (hg : g.IsSimple) (V : Vision Eg ξ) (lamp : Bool) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective Hg Z lamp, Q.MS = A ∧ Vision.StandaloneCorrelation V Z A ∧
      EveryCoefficient Z A (YM.FVA2.Teller.logNu 1) := by
  dsimp only
  obtain ⟨Q,hQ,hV,hs⟩ := nominated V (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)
    (WilsonCapturedPhysicalMSDatum.original g.core) lamp
  refine ⟨Q,hQ,hV,?_⟩
  intro n h d v within x k
  exact hs _ d v within x k
end SourceOnlyGraphSum
end YM.Answer.ContinuumLimit
