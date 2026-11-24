import YM.Integration.WilsonOriginalObservedRoseBornChiralFirstValue
import YM.Integration.WilsonOriginalObservedRoseBornChiralRegister

/-! The payable contribution of each of the four actual marked/unmarked binary inputs at the earlier report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralTariff
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

def levy (H:Hol G)(Q:Fin 2→SealR G)(e b:ℕ)(primary:Fin 2→Credit)(age:Fin 2→ℝ)
    (flag:Fin 2→Bool)(i:Fin 2):ℝ:=
  if flag i then (primary i).buy (age i) else (tariff H (Q i).ans (Q i).path e 0 b J J J).buy (age i)

def income (X:Courts (H:=H) (v:=v))(flag:Fin 2→Bool)(i:Fin 2):ℝ:=
  if flag i then (X i).fuel else cost e (dose (X i) 1)

def allowance (X:Courts (H:=H) (v:=v))(i:Fin 2):ℝ:=‖(X i).fuel‖+‖cost e (dose (X i) 1)‖

theorem posted (X:Courts (H:=H) (v:=v))(C:Fin 2→Credit)(b:ℕ)(flag:Fin 2→Bool)(i:Fin 2):
    amount 0 b C X (fun i=>dose (X i) 1) flag i=
      levy H Q e b C (fun i=>(X i).Age) flag i*income X flag i:=by
  cases go:flag i <;> simp only [amount,wallet,levy,income,go,Bool.false_eq_true,if_false,if_true]

private theorem split {I:Type*}[Fintype I](s:ℝ)(f a b:I→ℝ):
    (∏i,s*(f i*(a i*b i)))=(∏i,s*(f i*a i))*(∏i,b i):=by
  rw [←Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _=>by ring

theorem unitPrice (b e:ℕ)(w z:ℝ)(A B L:Fin 2→ℝ):
    tuition b e b w z (fun i=>A i*L i) B=tuition b e b w z A B*(∏i,L i):=by
  unfold tuition profiles
  rw [split]
  ring

def fee (H:Hol G)(Q:Fin 2→SealR G)(k e gain:ℕ)(φ:Wilt Q)(fees:Fin 2→ℝ)(y space tick:ℝ)
    (age:Fin 2→ℝ)(primary basal:Fin 2→Credit)(terminal:(Fin 2→Bool)→Credit)(flag:Fin 2→Bool):ℝ:=
  let z:=radius φ y
  let b:=10+gain
  2*(terminal flag).buy tick*tuition b e b space⁻¹ z (levy H Q e b primary age flag) fees+
    coinMat (ranksV flag k fun i=>(Q i).h) e*(∏i:Fin 2,factor 0 b z*(fees i*levy H Q e b basal age flag i))

theorem billed (gain:ℕ)(V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(φ:Wilt Q)(fees:Fin 2→ℝ)
    (y space:ℝ)(primary basal:Fin 2→Credit)(terminal:(Fin 2→Bool)→Credit)(m:ℕ)(flag:Fin 2→Bool):
    charge gain V X φ fees y space primary basal terminal m flag=
    fee H Q k e gain φ fees y space (epoch V m m) (fun i=>(X i).Age) primary basal terminal flag*
      (∏i,income X flag i):=by
  unfold WilsonOriginalObservedRoseBornChiralRetained.charge fee
  simp only [funext (posted X primary (10+gain) flag),funext (posted X basal (10+gain) flag)]
  rw [unitPrice,split]
  ring

theorem priced (gain:ℕ)(V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(φ:Wilt Q)(fees:Fin 2→ℝ)
    (y space:ℝ)(primary basal:Fin 2→Credit)(terminal:(Fin 2→Bool)→Credit)(m:ℕ)(flag:Fin 2→Bool):
    charge gain V X φ fees y space primary basal terminal m flag ≤
    ‖fee H Q k e gain φ fees y space (epoch V m m) (fun i=>(X i).Age) primary basal terminal flag‖*
      (∏i,allowance X i):=by
  rw [billed]
  apply (le_abs_self _).trans
  rw [abs_mul,Finset.abs_prod,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Finset.prod_le_prod (fun i _=>abs_nonneg _)
  intro i _
  unfold income allowance
  cases flag i <;> simp [Real.norm_eq_abs]

end YM.Integration.WilsonOriginalObservedRoseBornChiralTariff
