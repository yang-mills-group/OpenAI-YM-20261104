import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.RestaffedAngularStress
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.RestaffedPostTransfer
import YM.SignedWilsonExpansion.Public.Compass
import YM.Integration.WilsonOneFrameFixedReadings
set_option maxHeartbeats 850000
set_option maxRecDepth 8192
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Answer.ContinuumLimit
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Scale OPE OPE.Orbits
open SignedWilsonExpansion SignedWilsonExpansion.Kane SignedWilsonExpansion.StageG Camera SignedWilsonExpansion.Kane.Tilted Next.UVStress XSpace.Cirrus
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book PowerSeries Asymptotics
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open scoped Classical Topology
universe u
variable {G:Gauge}{H:G.Simple}{ε:ℝ}{e:Axis}{O:OrderS G}{E:Construction.{u} H ε e O}
variable {ξ:Extraction.Order} {V:Vision E ξ} {Z:WilsonPrescription G}{dial:Bool} {Q:Perspective H Z dial}

namespace RestaffedMeasuredStress
open Trace.Pith TraceExtension WilsonPositionHomogeneousFrame
open WilsonMacroscopicRichTwoDatePivot (active)

theorem staff (V : Vision E ξ) (m : ℕ) : ∀ᶠ r in trail,
    PhysMS.Frame.Staff (Y := V.pupil.Y) H V.pupil.last V.pupil.H r (V.pupil.J r) m := by
  filter_upwards [V.pupil.roomy,V.pupil.rises.eventually_ge_atTop m] with r room high
  exact (room.2.2.2 m high).1

theorem angle (V : Vision E ξ) : PlotX V.pupil.last V.pupil.H V.pupil.Y H (fun r => V.pupil.J r 4) :=
  (staff V 0).mono fun _ row => row.angle

theorem costs (V : Vision E ξ) (m : ℕ) : ∀ᶠ r in trail, chores r (V.pupil.J r 4) m :=
  PhysMS.Frame.leading_chores V.pupil.last V.pupil.J V.pupil.VFrame.2 m

theorem meter (V : Vision E ξ) : Coupling G (Trace.Pilot.wilson V.pupil.Z) := V.clockG

theorem staffStress (V : Vision E ξ) (i j : Axis) :
    Tendsto (fun r : ℝ => (V.pupil.J r 4).symm (r^4 • V.pupil.last.sector.energy i j)) trail
      (𝓝 (Pert.freeStress E.paths.family.labels i j)) :=
  RestaffedAngularStress.calibrated V.pupil.last H V.pupil.H V.pupil.bliss
    (angle V) (costs V) (meter V) i j

theorem postStress (V : Vision E ξ) (Z : WilsonPrescription G) (i j : Axis) :
    Tendsto (fun r : ℝ => (V.Post Z r 4).symm (r^4 • V.pupil.last.sector.energy i j)) trail
      (𝓝 (Pert.freeStress E.paths.family.labels i j)) := by
  exact YM.Integration.RestaffedPostTransfer.stress V.pupil.last V.pupil.J Z
    V.pupil.VFrame.2 V.pupil.VFrame.1 H i j (Pert.freeStress E.paths.family.labels i j) (staffStress V i j)


theorem ruler (V : Vision E ξ) (Z : WilsonPrescription G) (k d : ℕ) :
    (WilsonOneFrameFixedReadings.ruler V.pupil.last V.pupil.J Z V.sc).r k = V.sc.r k ∧
    (WilsonOneFrameFixedReadings.ruler V.pupil.last V.pupil.J Z V.sc).U k d = V.Post Z (V.sc.r k) d :=
  ⟨rfl,rfl⟩

theorem retained (V : Vision E ξ) : Pert.FirstExtension V.pupil.last V.sc := V.anchor

end RestaffedMeasuredStress
end YM.Answer.ContinuumLimit
end
