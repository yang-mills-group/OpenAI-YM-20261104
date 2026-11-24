import YM.Integration.WilsonOriginalObservedRoseBornChiralEars
import YM.Integration.WilsonIndependentMatchedRosterHome

/-! The three stable subwords at the actual pivot keep their own quarter
powers. The fourth subword is the true full fitted pair on the same vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralHome
open YM.WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedRosterLane WilsonIndependentMatchedCoverPairBudget
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedRosterSlots (entry wallet degree count)
open WilsonIndependentMatchedPhysicalComponent (volume price)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedPhysicalMasks (ranksV)
open WilsonSeparatedPrefixMovingReportedLanes (Courts row amount)
open WilsonSeparatedPrefixMovingReportedStableEdge (tuition)
open WilsonSeparatedPrefixMovingReportedStableLaw (reading)
open WilsonIndependentMatchedPhysicalSector (stamp)
open WilsonIndependentMovingRosterAllFineSeats (Elected)
open WilsonSeparatedPrefixMovingCalendar (epoch)

open WilsonSeparatedPrefixMovingReportedFaculty (sector)
open Trace Trace.Pilot FVA2 FVA2.Register Spec Extraction OPE PhysicalNext.Repeat.Legato
open Maxwell Maxwell.Free XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo
open WilsonMaxwellThermometerReflectedIncidence Table.Pairing
open WilsonMaxwellThermometerPublicStation (aperture)
open WilsonMaxwellThermometerSignedWallet (board)
open WilsonPhysicalChiralPairReading (Paid)
open WilsonPositionProgramReflectedPurse (shape)
open MS MS.WilsonBridge.Coupling
variable {G:Gauge}{e u₀:ℕ}{H:Hol G}
local notation "J" => Credit.leanC


open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonOriginalObservedRoseBornChiralEars (radius)
open WilsonIndependentMatchedRosterMasks (Bits choose quiet)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedPhysicalSector (field)
open private summed from YM.Integration.WilsonIndependentMatchedRosterPlanted

variable {Q:Fin 2→SealR G}{v:∀i,Rails (Q i).h 6 u₀ e}


open WilsonIndependentMatchedRosterTariff (factor)
open WilsonIndependentMatchedRosterChronology (mass)

def bill (V:Realm G (e+1) J)(m K:ℕ)(X:Courts (H:=H) (v:=v))(primary:Fin 2→Credit)
    (c:∀i,Verse (Q i).F)(flag:Fin 2→Bool)(z:ℝ)(fees:Fin 2→ℝ):ℝ:=
  coinMat (ranksV flag 6 fun i=>(Q i).h) e *
    (∏i:Fin 2,factor 0 12 z*(fees i * amount 0 12 primary X c flag i)) *
    (paceT V.draws.S m K)^((((∑i:Fin 2,count (flag i)):ℕ):ℝ)/4)

theorem original (Q:Fin 2→SealR G)(v:∀i,Rails (Q i).h 6 u₀ e)(width:12 ≤ u₀):
    ∃primary:Fin 2→Credit,∀(V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(m K N:ℕ),
      stamp V X m K N → ∀(φ:Wilt Q)(fees:Fin 2→ℝ)(y:ℝ)(space:ℝ),Bough Q φ y space fees →
      ∀(c:∀i,Verse (Q i).F)(flag:Fin 2→Bool)(o:CellR),
        response e 0 (sector V flag X c φ y o m m N) (bill V m K X primary c flag (radius φ y) fees):=by
  obtain ⟨primary,book⟩:=WilsonSeparatedPrefixMovingReportedLanes.original H Q v 0 12 (by simpa using width)
  refine ⟨primary,?_⟩
  intro V X m K N stamp φ fees y space house c flag o
  have actual:=book V X m K N φ fees y o stamp house.lanes c flag
  have radial (i:Fin 2):radiusH (φ i) 1 y ≤ radius φ y:=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _=>abs_nonneg (radiusH (φ j) 1 y)) (Finset.mem_univ i))
  have bought:=WilsonIndependentMatchedRosterHome.original V m (K-m) N (fun i=>(Q i).h)
    (fun i=>count (flag i)) (fun i=>degree (flag i) 6 (Q i).h) φ (row flag X c φ y o)
    (paceT V.draws.S m K) y (radius φ y) o (amount 0 12 primary X c flag) fees
    (pace_pos ..) radial (fun i=>(actual i).1) house.lanes (fun i=>(actual i).2)
  have carried:sector V flag X c φ y o m m N=mass (row flag X c φ y o) 0:=by
    unfold WilsonSeparatedPrefixMovingReportedFaculty.sector WilsonSeparatedPrefixMovingReportedStableLaw.reading
    rw [cruises,dif_neg (lt_irrefl m),Nat.sub_self]
  rw [carried]
  have score:Flush e 0 1 (mass (row flag X c φ y o) 0) (bill V m K X primary c flag (radius φ y) fees):=by
    simpa only [bill,ranksV,pow_one] using bought.2
  exact ⟨score,WilsonIndependentMatchedCoverJoined.unit score⟩

end YM.Integration.WilsonOriginalObservedRoseBornChiralHome
