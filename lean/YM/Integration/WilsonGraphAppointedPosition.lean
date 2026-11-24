import YM.Integration.WilsonGraphAppointedMeasurementLaws
import YM.Integration.WilsonGraphAppointedPositionSelection
import YM.Integration.WilsonGraphAppointedPositionReal
import YM.Integration.WilsonGraphAppointedTriangleReading
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedConversionValid

namespace YM.Answer.ContinuumLimit.ElectedMeasurement

open Function Filter Set Asymptotics PowerSeries
open Lattice RG MeasureTheory Wilson Extraction Climb Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level
open SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane
open SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Integration.Election Integration.Election.Frames
open Order Spin SignedWilsonExpansion.StageG XSpace.Cirrus Entree Future
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open Integration.GradedFar Integration.GradedFar.Tariff
open _root_.IssuedBridge
open scoped Topology BigOperators Classical ContDiff

open FVA2.GradedFar FVA2.Dframe
universe u
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ}
variable {e : Axis} {O : OrderS g.core} {E : Construction.{u} H ε e O}
variable {ξ : Extraction.Order}




set_option maxHeartbeats 1600000 in
theorem appointed (hg : g.IsSimple) (V : Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let menu := _root_.IssuedMaxwell.ElectedPrescription.prior g hg
    YangMills.MSbar.CorrelationOnly.appointed menu.val
      (_root_.IssuedBridge.PostedAppointedConversionValid.realized hg true)
      (YangMills.wilsonFamily E.paths.family) (YangMills.hierarchy V.pupil.last V.pupil.P)
      (publicMeasurement hg V Z Q) := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let law := Integration.WilsonPositionHomogeneousCoefficients.purchased Z
    (_root_.IssuedBridge.PostedAppointedConversionFields.elected hg true)
  refine ⟨preFrame V Z, preNormalized hg V Q, preLocallyUnique hg V Q,
    preUnital V Z Q, preNested V Z Q, preReal V Z Q, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with r hr
    exact ⟨preTriangleIntegrable hg V Z hr,
      (congrFun (publicClock hg V Z Q) r).trans (publicTriangleClock hg V Q r)⟩
  · intro d
    filter_upwards [numericalFrame V Z Q law d] with r received
    intro v
    change frame V Z r d v = preFrame V Z r d
      ((_root_.IssuedBridge.PostedNumericalAdjustment.filed Z law).value d (clock V Z r) v)
    exact received v

end YM.Answer.ContinuumLimit.ElectedMeasurement
