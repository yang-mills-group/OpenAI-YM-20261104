import YangMills.WilsonProof.NativeSupport.IssuedBridge.WilsonQ198AppointedPhaseValue
import YM.Integration.WilsonLogarithmicFourthPower

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


theorem _root_.YM.Integration.WilsonElectedFourthPowerClock.original
    (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true) (m : ℕ) :
    (fun r : ℝ => r ^ 4) =o[YM.Trace.Pilot.trail] (fun r => V.T Z r ^ m) := by
  have paid := (V.certificate Q).calendar.clock
  exact YM.Integration.WilsonLogarithmicFourthPower.fromRunning
    (inv_pos.mpr (YM.Gauge.slopeConstant_pos H)) paid.positive (paid.conforms H) paid.running m


theorem _root_.YM.Integration.WilsonElectedFourthPowerClock.ratio
    (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true) (m : ℕ) :
    Tendsto (fun r : ℝ => r ^ 4 / (V.T Z r) ^ m) YM.Trace.Pilot.trail (𝓝 0) :=
  (YM.Integration.WilsonElectedFourthPowerClock.original V Z Q m).tendsto_div_nhds_zero

end YM.Answer.ContinuumLimit.ElectedMeasurement

