import YM.Integration.WilsonOriginalObservedRoseBornChiralBudget

/-! The payable contribution of each of the four actual marked/unmarked binary inputs at the earlier report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralToll
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

def excess (H:Hol G)(Q:Fin 2→SealR G)(k e gain:ℕ)(φ:Wilt Q)(fees:Fin 2→ℝ)
    (y space δ tick:ℝ)(ages:Fin 2→ℝ)(p b un:Fin 2→Credit)(t:(Fin 2→Bool)→Credit):ℝ:=
  let f:=fun i=>‖fixed H Q e φ fees y ages i‖
  let s:=fun i=>‖mutable Q φ fees y ages un i‖
  let other:=∑j∈Finset.univ.erase (WilsonIndependentMatchedRosterMasks.quiet 1),
    ‖fee H Q k e gain φ fees y space tick ages p b t (choose 1 j)‖
  other+2*(s 0*(δ*s 1+f 1)+f 0*s 1)

theorem paid (gain:ℕ)(V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(φ:Wilt Q)(fees:Fin 2→ℝ)
    (y space δ:ℝ)(pos:0 ≤ δ)(m:ℕ)(p b un:Fin 2→Credit)(t:(Fin 2→Bool)→Credit):
    amountDue gain V X φ fees y space δ m p b un t ≤
      excess H Q k e gain φ fees y space δ (epoch V m m) (fun i=>(X i).Age) p b un t*
      (∏i,allowance X i):=by
  let tick:=epoch V m m
  let ages:=fun i=>(X i).Age
  let w:=∏i,allowance X i
  let F:=fun i=>fittedFee (X i) (φ i) (fees i) y
  let S:=fun i=>unaryBase (X i) (un i) (φ i) (fees i) y
  let f:=fun i=>‖fixed H Q e φ fees y ages i‖
  let s:=fun i=>‖mutable Q φ fees y ages un i‖
  let other:=∑j∈Finset.univ.erase (WilsonIndependentMatchedRosterMasks.quiet 1),
    ‖fee H Q k e gain φ fees y space tick ages p b t (choose 1 j)‖
  let upper:=portfolio gain V X φ fees y space p b t m
  have fg (i:Fin 2):‖F i‖ ≤ f i*allowance X i:=WilsonOriginalObservedRoseBornChiralUnaryCash.ordinary X φ fees y i
  have sg (i:Fin 2):‖S i‖ ≤ s i*allowance X i:=WilsonOriginalObservedRoseBornChiralUnaryCash.stable X φ fees y un i
  have ss:S 0*S 1 ≤ (s 0*s 1)*w:=paired (allowance X) (sg 0) (sg 1)
  have sf:S 0*F 1 ≤ (s 0*f 1)*w:=paired (allowance X) (sg 0) (fg 1)
  have fs:F 0*S 1 ≤ (f 0*s 1)*w:=paired (allowance X) (fg 0) (sg 1)
  have q₁:upper ≤ other*w:=by
    unfold upper other portfolio
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _=>WilsonOriginalObservedRoseBornChiralTariff.priced gain V X φ fees y space p b t m _
  have o:S 0*(δ*S 1+F 1)+F 0*S 1 ≤ (s 0*(δ*s 1+f 1)+f 0*s 1)*w:=calc
    _=δ*(S 0*S 1)+S 0*F 1+F 0*S 1:=by ring
    _ ≤ δ*((s 0*s 1)*w)+(s 0*f 1)*w+(f 0*s 1)*w:=add_le_add (add_le_add (mul_le_mul_of_nonneg_left ss pos) sf) fs
    _ = _ :=by ring
  change upper+2*(S 0*(δ*S 1+F 1)+F 0*S 1) ≤ (other+2*(s 0*(δ*s 1+f 1)+f 0*s 1))*w
  calc
    _ ≤ other*w+2*((s 0*(δ*s 1+f 1)+f 0*s 1)*w):=add_le_add q₁ (mul_le_mul_of_nonneg_left o (by norm_num))
    _ = _ :=by ring

theorem original (M:Master H)(Q:Fin 2→SealR G)(cap:capP Q=10)(v:∀i,Rails (Q i).h k u₀ e)
    (height seats gain:ℕ)(surplus:2 ≤ gain)(stage:2*k ≤ 10+gain)(room:10+gain ≤ seats)(width:10+gain ≤ u₀)(heat:1 ≤ e):
    ∃p b un:Fin 2→Credit,∃t:(Fin 2→Bool)→Credit,
    ∀(V:Realm G (e+1) J),Elected M V height seats → ∀(X Y:Courts (H:=H) (v:=v))
    (m K N:ℕ),stamp V X m K N → stamp V Y m K N → (∀i,(X i).L=(Y i).L) →
    (∀i,home (Q i) (X i)=home (Q i) (Y i)) → V.anchor ≤ m → m ≤ K → K ≤ N →
    (∀i,On (Q i).h (X i).pt) → (∀i,On (Q i).h (Y i).pt) →
    ∀(φ:Wilt Q)(fees:Fin 2→ℝ)(y space:ℝ),Bough Q φ y space fees → ∀(o:CellR)(ω:Fin 0→YForest G),
    let δ:=(paceT V.draws.S m K)^(1/4:ℝ)
    let billing:=fun (Z:Courts (H:=H) (v:=v))=>
      excess H Q k e gain φ fees y space δ (epoch V m m) (fun i=>(Z i).Age) p b un t*(∏i,allowance Z i)
    ‖first V X φ m K N y o ω-first V Y φ m K N y o ω‖ ≤ δ*(billing X+billing Y):=by
  obtain ⟨p,b,un,t,price⟩:=WilsonOriginalObservedRoseBornChiralFirstRate.original M Q cap v height seats gain
    surplus stage room width heat
  refine ⟨p,b,un,t,?_⟩
  intro V sold X Y m K N posted registered school votes floor past live goodX goodY φ fees y space house o ω δ billing
  have pos:0≤δ:=Real.rpow_nonneg (pace_pos V.draws.S m K).le _
  have loss (Z:Courts (H:=H) (v:=v))(dated:stamp V Z m K N)(good:∀i,On (Q i).h (Z i).pt):
      ‖first V Z φ m K N y o ω-WilsonOriginalObservedRoseBornChiralHearing.projected V Z φ m K N y o ω‖ ≤ δ*billing Z:=
    (price V sold Z m K N dated floor past live good φ fees y space house o ω).trans
      (mul_le_mul_of_nonneg_left (paid gain V Z φ fees y space δ pos m p b un t) pos)
  have same:=WilsonOriginalObservedRoseBornChiralPivot.original V X Y φ m K N posted registered school votes y o ω
  rw [mul_add]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (WilsonOriginalObservedRoseBornChiralHearing.projected V X φ m K N y o ω) _).trans
    (add_le_add (loss X posted goodX) ?_)
  rw [same,norm_sub_rev]
  exact loss Y registered goodY

end YM.Integration.WilsonOriginalObservedRoseBornChiralToll
