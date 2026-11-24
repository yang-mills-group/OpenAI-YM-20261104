import YM.Integration.WilsonOriginalObservedRoseBornChiralTariff

/-! The payable contribution of each of the four actual marked/unmarked binary inputs at the earlier report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralUnaryCash
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
variable {G:Gauge}{k e u₀:ℕ}{H:Hol G}
local notation "J" => Credit.leanC


open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonOriginalObservedRoseBornChiralEars (radius)
open WilsonIndependentMatchedRosterMasks (Bits choose quiet)
open WilsonIndependentMatchedPhysicalReturn (ordinary)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedPhysicalSector (field)
open private summed from YM.Integration.WilsonIndependentMatchedRosterPlanted

variable {Q:Fin 2→SealR G}{v:∀i,Rails (Q i).h k u₀ e}

open WilsonOriginalObservedRoseBornChiralRankHome (bill)
open WilsonOriginalObservedRoseBornChiralRankOffice (wage)

open WilsonSeparatedPrefixMovingRetainedFaculty (quarter)
open WilsonIndependentMatchedRosterTariff (factor)
open WilsonIndependentMatchedProxyIncome (cost tariff)
open WilsonOriginalObservedRoseBornChiralRetained (charge)
open WilsonIndependentMatchedRosterPowers (profiles)
open WilsonIndependentMatchedRosterSlots (wallet)
open WilsonOriginalObservedRoseBornChiralProper (fittedFee)
open WilsonOriginalObservedRoseBornChiralFirstRate (unaryBase)
open WilsonOriginalObservedRoseBornChiralProducts (centered)

open WilsonOriginalObservedRoseBornChiralTariff (allowance)
open WilsonIndependentMatchedRosterLane (chargeBelow)

def fixed (H:Hol G)(Q:Fin 2→SealR G)(e:ℕ)(φ:Wilt Q)(fees:Fin 2→ℝ)(y:ℝ)(life:Fin 2→ℝ)(i:Fin 2):ℝ:=
  chargeBelow (φ i) 0 (Q i).h 1 y ((tariff H (Q i).ans (Q i).path e 0 0 J J J).buy (life i)) (fees i)

def mutable (Q:Fin 2→SealR G)(φ:Wilt Q)(fees:Fin 2→ℝ)(y:ℝ)(life:Fin 2→ℝ)(un:Fin 2→Credit)(i:Fin 2):ℝ:=
  chargeBelow (φ i) 0 (Q i).h 1 y ((un i).buy (life i)) (fees i)

theorem ordinary (X:Courts (H:=H) (v:=v))(φ:Wilt Q)(fees:Fin 2→ℝ)(y:ℝ)(i:Fin 2):
    ‖fittedFee (X i) (φ i) (fees i) y‖ ≤ ‖fixed H Q e φ fees y (fun i=>(X i).Age) i‖*allowance X i:=by
  have same:fittedFee (X i) (φ i) (fees i) y=
      fixed H Q e φ fees y (fun i=>(X i).Age) i*cost e (dose (X i) 1):=by
    unfold fittedFee fixed chargeBelow
    ring
  rw [same,norm_mul]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (norm_nonneg _)

theorem stable (X:Courts (H:=H) (v:=v))(φ:Wilt Q)(fees:Fin 2→ℝ)(y:ℝ)(un:Fin 2→Credit)(i:Fin 2):
    ‖unaryBase (X i) (un i) (φ i) (fees i) y‖ ≤ ‖mutable Q φ fees y (fun i=>(X i).Age) un i‖*allowance X i:=by
  have same:unaryBase (X i) (un i) (φ i) (fees i) y=
      mutable Q φ fees y (fun i=>(X i).Age) un i*(X i).fuel:=by
    unfold unaryBase mutable chargeBelow
    ring
  rw [same,norm_mul]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _)

theorem paired {a b A B:ℝ}(w:Fin 2→ℝ)(left:‖a‖ ≤ A*w 0)(right:‖b‖ ≤ B*w 1):a*b ≤ A*B*(∏i,w i):=by
  calc
    a*b ≤ ‖a‖*‖b‖:=by rw [←norm_mul];exact le_abs_self _
    _ ≤ (A*w 0)*(B*w 1):=mul_le_mul left right (norm_nonneg _) ((norm_nonneg _).trans left)
    _ = _ :=by rw [Fin.prod_univ_two];ring

theorem nonnegative (X:Courts (H:=H) (v:=v))(i:Fin 2):0 ≤ allowance X i:=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

end YM.Integration.WilsonOriginalObservedRoseBornChiralUnaryCash
