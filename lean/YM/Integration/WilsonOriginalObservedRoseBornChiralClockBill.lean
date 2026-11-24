import YM.Integration.WilsonOriginalObservedRoseBornChiralToll
import YM.Integration.WilsonOriginalObservedRoseBornChiralCoupon

/-! The payable contribution of each of the four actual marked/unmarked binary inputs at the earlier report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralClockBill
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

open WilsonOriginalObservedRoseBornChiralTariff (fee)
open WilsonOriginalObservedRoseBornChiralUnaryCash (fixed mutable paired)
open WilsonOriginalObservedRoseBornChiralValue (gross)
open WilsonOriginalObservedRoseBornChiralDelta (portfolio)
open WilsonOriginalObservedRoseBornChiralSwitch (amountDue)
open WilsonOriginalObservedRoseBornChiralHearing (first)
open WilsonOriginalObservedRoseBornChiralProper (atGrade)

structure Dates where
  bound:ℝ
  tick:ℝ
  span:ℝ
  fraction:ℝ

structure Funded (x:Dates):Prop where
  floor:1≤x.bound
  clock:1≤x.tick
  endclock:x.tick≤x.bound
  age:1≤x.span
  endage:x.span≤x.bound
  part:0≤x.fraction
  top:x.fraction≤1

def Priced (f:Dates→ℝ):Prop:=∃c:Credit,∀x,Funded x→‖f x‖≤c.buy x.bound

theorem constant (a:ℝ):Priced (fun _=>a):=by
  refine ⟨⟨0,max 1 ‖a‖,le_max_left _ _⟩,fun _ _=>?_⟩
  simpa only [Credit.buy,pow_zero,mul_one] using (le_max_right 1 ‖a‖)

theorem time (c:Credit):Priced (fun x=>c.buy x.tick):=by
  refine ⟨c,fun x h=>?_⟩
  rw [Real.norm_of_nonneg (zero_le_one.trans (c.purchase h.clock))]
  exact c.elder h.clock h.endclock

theorem runway (c:Credit):Priced (fun x=>c.buy x.span):=by
  refine ⟨c,fun x h=>?_⟩
  rw [Real.norm_of_nonneg (zero_le_one.trans (c.purchase h.age))]
  exact c.elder h.age h.endage

theorem scale:Priced Dates.fraction:=by
  refine ⟨Credit.unit,fun x h=>?_⟩
  simpa only [Credit.unit_cost,Real.norm_of_nonneg h.part] using h.top

theorem add {f g:Dates→ℝ}(u:Priced f)(v:Priced g):Priced (fun x=>f x+g x):=by
  obtain ⟨a,p⟩:=u
  obtain ⟨b,q⟩:=v
  exact ⟨a.plus b,fun x h=>(norm_add_le _ _).trans ((add_le_add (p x h) (q x h)).trans (a.fuel b h.floor))⟩

theorem mul {f g:Dates→ℝ}(u:Priced f)(v:Priced g):Priced (fun x=>f x*g x):=by
  obtain ⟨a,p⟩:=u
  obtain ⟨b,q⟩:=v
  refine ⟨a.prodC b,fun x h=>?_⟩
  rw [norm_mul,Credit.products]
  exact mul_le_mul (p x h) (q x h) (norm_nonneg _) (zero_le_one.trans (a.purchase h.floor))

theorem absolute {f:Dates→ℝ}(u:Priced f):Priced (fun x=>‖f x‖):=by
  obtain ⟨a,p⟩:=u
  exact ⟨a,fun x h=>by simpa only [norm_norm] using p x h⟩

theorem sum {I:Type*}(s:Finset I)(f:I→Dates→ℝ)(p:∀i∈s,Priced (f i)):
    Priced (fun x=>∑i∈s,f i x):=by
  classical
  induction s using Finset.induction_on with
  | empty =>simpa only [Finset.sum_empty] using constant 0
  | @insert i s fresh ih =>
    have tail:=ih (fun j hj=>p j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert fresh] using add (p i (Finset.mem_insert_self i s)) tail

theorem product {I:Type*}(s:Finset I)(f:I→Dates→ℝ)(p:∀i∈s,Priced (f i)):
    Priced (fun x=>∏i∈s,f i x):=by
  classical
  induction s using Finset.induction_on with
  | empty =>simpa only [Finset.prod_empty] using constant 1
  | @insert i s fresh ih =>
    have tail:=ih (fun j hj=>p j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert fresh] using mul (p i (Finset.mem_insert_self i s)) tail

theorem nativeFee (H:Hol G)(Q:Fin 2→SealR G)(k e gain:ℕ)(φ:Wilt Q)(fees:Fin 2→ℝ)(y space:ℝ)
    (p b:Fin 2→Credit)(t:(Fin 2→Bool)→Credit)(flag:Fin 2→Bool):
    Priced (fun x=>fee H Q k e gain φ fees y space x.tick (fun _=>x.span) p b t flag):=by
  let n:=10+gain
  let r:=radius φ y
  have each (C:Fin 2→Credit)(i:Fin 2):Priced
      (fun x=>WilsonOriginalObservedRoseBornChiralTariff.levy H Q e n C (fun _=>x.span) flag i):=by
    cases h:flag i <;> simp only [WilsonOriginalObservedRoseBornChiralTariff.levy,h,Bool.false_eq_true,if_false,if_true] <;>
      exact runway _
  have series (C:Fin 2→Credit):Priced
      (fun x=>∏i:Fin 2,factor 0 n r*(fees i*WilsonOriginalObservedRoseBornChiralTariff.levy H Q e n C (fun _=>x.span) flag i)):=
    product Finset.univ _ (fun i _=>mul (constant _) (mul (constant _) (each C i)))
  unfold fee tuition profiles
  exact add (mul (mul (constant _) (time _)) (mul (constant _) (series p))) (mul (constant _) (series b))

theorem original (H:Hol G)(Q:Fin 2→SealR G)(k e gain:ℕ)(φ:Wilt Q)(fees:Fin 2→ℝ)(y space:ℝ)
    (p b un:Fin 2→Credit)(t:(Fin 2→Bool)→Credit):
    Priced (fun x=>WilsonOriginalObservedRoseBornChiralToll.excess H Q k e gain φ fees y space x.fraction x.tick
      (fun _=>x.span) p b un t):=by
  have fixed₀ (i:Fin 2):Priced (fun x=>‖fixed H Q e φ fees y (fun _=>x.span) i‖):=by
    unfold fixed chargeBelow
    exact absolute (mul (constant _) (mul (constant _) (mul (constant _) (runway _))))
  have moving (i:Fin 2):Priced (fun x=>‖mutable Q φ fees y (fun _=>x.span) un i‖):=by
    unfold mutable chargeBelow
    exact absolute (mul (constant _) (mul (constant _) (mul (constant _) (runway _))))
  unfold WilsonOriginalObservedRoseBornChiralToll.excess
  refine add (sum _ _ (fun j _=>absolute (nativeFee H Q k e gain φ fees y space p b t (choose 1 j)))) ?_
  exact mul (constant 2) (add (mul (moving 0) (add (mul scale (moving 1)) (fixed₀ 1))) (mul (fixed₀ 0) (moving 1)))

theorem ticket {d:ℕ}(F:Labels.Frame G d)(e:ℕ)(base rate:Credit)(A:Alma F→ℝ):
    Priced (fun x=>‖WilsonOriginalObservedRoseBornChiralCoupon.coin F e base rate x.tick x.span A‖):=by
  unfold WilsonOriginalObservedRoseBornChiralCoupon.coin
  exact absolute (mul (mul (constant _) (time _)) (add (mul (runway _) (constant _)) (constant _)))

end YM.Integration.WilsonOriginalObservedRoseBornChiralClockBill
