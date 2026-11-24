import YM.Integration.WilsonGraphAppointedPositionUnitTriangle
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.UniversalLabels
import YM.Integration.WilsonPositionThermometerReading
set_option autoImplicit false
noncomputable section

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



theorem appointedTriangleLabels (hg : g.IsSimple) :
    (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle.labels =
      Rose.tag g.core := by
  let t := (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle
  have h := _root_.IssuedMaxwell.UniversalLabels.original g t
  change ![t.T,t.UatSix,t.UatSix] = ![Rose.toll g.core,Rose.tin g.core,Rose.tin g.core]
  rw [h.1,h.2.2.1]
  rfl

theorem appointedTriangleFace (hg : g.IsSimple) (s : Finset (Fin 3)) :
    (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle.face s =
      Rose.missing (Rose.tag g.core) s := by
  let t := (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle
  have h := _root_.IssuedMaxwell.UniversalLabels.original g t
  funext i
  change (if i ∈ s then t.labels i else t.unit) =
    (if i ∈ s then Rose.tag g.core i else leaf g.core 6)
  rw [h.2.2.2,appointedTriangleLabels hg]
  rfl

theorem preTriangleMoment (hg : g.IsSimple) (V : Vision E ξ)
    (Z : WilsonPrescription g.core) (r : ℝ) (s : Finset (Fin 3)) (x : Points 3) :
    YangMills.MSbar.positionMoment (YangMills.hierarchy V.pupil.last V.pupil.P)
      (preFrame V Z) r 6 ((_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle.face s) x =
    Integration.WilsonPositionThermometerReading.sample V.pupil.last (V.Pre Z) r x s := by
  rw [appointedTriangleFace hg s]
  rfl

theorem preTriangleConnected (hg : g.IsSimple) (V : Vision E ξ)
    (Z : WilsonPrescription g.core) (r : ℝ) (x : Points 3) :
    (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle.connected
      (YangMills.MSbar.positionMoment (YangMills.hierarchy V.pupil.last V.pupil.P)
        (preFrame V Z) r 6) x =
    Integration.WilsonPositionThermometerConnected.value
      (Integration.WilsonPositionThermometerReading.sample V.pupil.last (V.Pre Z) r x) := by
  unfold YangMills.MSbar.Position.Triangle.connected YangMills.MSbar.Position.connectedThree
    Integration.WilsonPositionThermometerConnected.value
  simp only [preTriangleMoment hg V Z, mul_assoc]

theorem preTriangleIntegrable (hg : g.IsSimple) (V : Vision E ξ)
    (Z : WilsonPrescription g.core) {r : ℝ} (hr : 0 < r) :
    let t := (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle
    let m := YangMills.MSbar.positionMoment (n := 3) (YangMills.hierarchy V.pupil.last V.pupil.P)
      (preFrame V Z) r 6
    Integrable (fun x => t.profile x * t.connected m x) := by
  let t := (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle
  apply _root_.YM.Test.smearing t.profile
  have h (s : Finset (Fin 3)) :=
    Integration.WilsonPositionPrescribedScreen.smooth V.pupil.last (V.Pre Z) (t.face s) hr
  exact ((h Finset.univ).sub
    ((((h {0,1}).mul (h {2})).add ((h {0,2}).mul (h {1}))).add
      ((h {1,2}).mul (h {0})))).add (((continuousOn_const.mul (h {0})).mul (h {1})).mul (h {2}))

theorem preTriangleMeasure (hg : g.IsSimple) (V : Vision E ξ) (r : ℝ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let t := (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle
    t.measure (YangMills.MSbar.positionMoment (YangMills.hierarchy V.pupil.last V.pupil.P)
      (preFrame V Z) r 6) = (Signal V Z r).re := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let t := (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle
  let m := YangMills.MSbar.positionMoment (n := 3) (YangMills.hierarchy V.pupil.last V.pupil.P)
    (preFrame V Z) r 6
  change (∫ x : Points 3, t.profile x * t.connected m x).re =
    (∫ x : Points 3, Rose.test Z.criterion x *
      Integration.WilsonPositionThermometerConnected.value
        (Integration.WilsonPositionThermometerReading.sample V.pupil.last (V.Pre Z) r x)).re
  apply congrArg Complex.re
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Rose.tests,appointedTriangleProfile hg x,preTriangleConnected hg V Z r x]

theorem publicTriangleClock (hg : g.IsSimple) (V : Vision E ξ)
    {lamp : Bool} (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) lamp)
    (r : ℝ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let t := (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle
    V.T Z r = t.measure (YangMills.MSbar.positionMoment
      (YangMills.hierarchy V.pupil.last V.pupil.P) (preFrame V Z) r 6) / t.cT := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let t := (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle
  exact (preClockAtFiledTriangle hg V Q r).trans
    (congrArg (fun x : ℝ => x / t.cT) (preTriangleMeasure hg V r).symm)

end YM.Answer.ContinuumLimit.ElectedMeasurement
end

