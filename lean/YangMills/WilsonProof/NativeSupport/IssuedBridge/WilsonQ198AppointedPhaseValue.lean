import YangMills.WilsonProof.NativeSupport.IssuedBridge.WilsonQ198PostFrankValue
import YM.Integration.WilsonGraphAppointedStationaryPrices
import YM.Integration.WilsonQ198PhysicalPhaseWords

noncomputable section
namespace IssuedBridge.WilsonQ198AppointedPhaseValue

open YM YM.Integration YM.FVA2.Dframe YM.FVA2.O.Score

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
open Integration.GradedFar.Tariff.Sunshine
open WilsonPositionHomogeneousComparison
open scoped Topology BigOperators Classical ContDiff

universe u
variable {G : Gauge} {H : G.Simple} {ε : ℝ} {e : Axis} {O : OrderS G}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}
variable (Z : WilsonPrescription G) (V : Vision E ξ) (Q : Perspective H Z true)
local notation "t" => V.T Z
local notation "X" => FVA2.Scale.Measure.outlook Z.scheme Z.criterion



include Q in
theorem original {n : ℕ} (K : Set (Points n)) (compact : IsCompact K)
    (safe : K ⊆ conf n) (γ : ℝ) (hγ : γ < 4) (h : ℕ) (v : ListInput G n h) :
    WilsonQ198PhysicalPhaseWords.Priced V.pupil.last (V.Post Z)
      K (fun _ x _ => x) γ [] h v := by
  exact IssuedBridge.WilsonQ198PostFrankValue.original (b := 1) H E.pillars
    E.receipts.receiptsP.1 E.receipts.receiptsP.2 (by decide) V.pupil.last
    V.pupil.pillar V.pupil.P V.pupil.J Z V.pupil.VFrame.2 V.pupil.VFrame.1
    compact safe (V.certificate Q).calendar.clock hγ
    (show ∀ᶠ r : ℝ in trail, 0 < r from self_mem_nhdsWithin) h v

end IssuedBridge.WilsonQ198AppointedPhaseValue
