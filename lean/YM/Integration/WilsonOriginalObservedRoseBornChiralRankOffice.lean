import YM.Integration.WilsonOriginalObservedRoseBornChiralRank
import YM.Integration.WilsonOriginalObservedRoseBornChiralRankHome

/-! The two reflected ears in their native detector-then-upper order, using any already elected compact bulb. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralRankOffice
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
def wage (gain:ℕ)(V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(φ:Wilt Q)(fees:Fin 2→ℝ)(y space:ℝ)
    (primary:Fin 2→Credit)(terminal:(Fin 2→Bool)→Credit)(m:ℕ)(flag:Fin 2→Bool):ℝ:=
  2*(terminal flag).buy (epoch V m m)*(paceT V.draws.S m m)^gain*
    tuition (10+gain) e (10+gain) space⁻¹ (radius φ y) (amount 0 (10+gain) primary X (fun i=>dose (X i) 1) flag) fees



theorem original (M:Master H)(Q:Fin 2→SealR G)(cap:capP Q=10)
    (v:∀i,Rails (Q i).h k u₀ e)(height seats gain:ℕ)(surplus:2 ≤ gain)(stage:2*k ≤ 10+gain)
    (room:10+gain ≤ seats)(width:10+gain ≤ u₀)
    (a:Axis)(x:E4)(bulb:Bulb (site x) a)(y:ℝ):
    ∃φ:Wilt Q,∃fees:Fin 2→ℝ,∃space:ℝ,∃primary basal:Fin 2→Credit,∃terminal:(Fin 2→Bool)→Credit,
      (∀i,(φ i).ψ.val=shape a x bulb i) ∧ Bough Q φ y space fees ∧
      ∀(V:Realm G (e+1) J)(_sold:Elected M V height seats)(X:Courts (H:=H) (v:=v))
        (m K N:ℕ),stamp V X m K N → V.anchor ≤ m → m ≤ K → K ≤ N →
        (∀i,On (Q i).h (X i).pt) → ∀(o:CellR)(q:ℕ),q ≤ e → ∀ω:Fin 0→YForest G,
        ‖(cruises V.draws V.paid N (capP Q) K m (ordinary V.draws X φ m K y o)).2 q 0 ω‖ ≤
          ∑j:Bits 1,
            (wage gain V X φ fees y space primary terminal m (choose 1 j) +
            bill (10+gain) V m K X basal (fun i=>dose (X i) 1) (choose 1 j) (radius φ y) fees):=by
  obtain ⟨primary,terminal,edges⟩:=WilsonSeparatedPrefixMovingReportedFaculty.original
    (n:=0) M Q v (10+gain) gain height seats (by simpa using stage) (by omega) (by omega) (by omega) surplus
  obtain ⟨φ,source,fees,geometric⟩:=WilsonPositionProgramReflectedPurse.original Q a x bulb y
  obtain ⟨space,book⟩:=geometric.exists
  obtain ⟨basal,homebound⟩:=WilsonOriginalObservedRoseBornChiralRankHome.original (H:=H) Q v (10+gain) width
  refine ⟨φ,fees,space,primary,basal,terminal,source,book,?_⟩
  have radial (i:Fin 2):radiusH (φ i) 1 y ≤ radius φ y:=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _=>abs_nonneg (radiusH (φ j) 1 y)) (Finset.mem_univ i))
  have positive:0<space⁻¹:=inv_pos.mpr (lt_of_lt_of_le zero_lt_one book.pos)
  intro V sold X m K N filed floor past live sound o q qa ω
  rw [WilsonOriginalObservedRoseBornChiralRank.original V X m K N filed past live φ fees book.lanes sound y o]
  simp only [Prod.snd_sum,Finset.sum_apply]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  let flag:=choose 1 j
  let c:=fun i=>dose (X i) 1
  let upper:=sector V flag X c φ y o m K N
  let lower:=sector V flag X c φ y o m m N
  have between:=((edges V sold X m m K N filed floor le_rfl past live φ fees y
    (radius φ y) space⁻¹ o positive book.seats radial book.lanes c flag).2.2 q qa ω)
  simp only [cap] at between
  have initial:=(homebound V X m K N filed φ fees y space book c flag o).2 q qa ω
  calc
    ‖upper.2 q 0 ω‖ = ‖((upper-lower)+lower).2 q 0 ω‖ := by rw [sub_add_cancel]
    _ ≤ ‖(upper-lower).2 q 0 ω‖+‖lower.2 q 0 ω‖ := norm_add_le _ _
    _ ≤ _ := add_le_add between initial

end YM.Integration.WilsonOriginalObservedRoseBornChiralRankOffice
