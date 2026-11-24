import YM.Integration.WilsonSeparatedPrefixMovingReportedLanes
import YM.Integration.WilsonSeparatedPrefixMovingReportedStableSum
import YM.Integration.WilsonIndependentMovingRosterAllFineSeats
import YM.Integration.WilsonIndependentMatchedPhysicalSector
import YM.Integration.WilsonIndependentMatchedPhysicalComponent
import YM.Integration.WilsonIndependentMatchedPhysicalArm
import YM.Integration.WilsonIndependentMatchedPhysicalCourt
import YM.Integration.WilsonIndependentMatchedPhysicalMasks
import YM.Integration.WilsonIndependentMatchedAccruedRestart
/-! Charge of a literal mixed stable sector on the shared physical K-to-host shoulder. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingReportedFaculty
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
variable {G:Gauge}{n k e u₀:ℕ}{H:Hol G}{Q:Fin ((n+1)+1)→SealR G}{v:∀i,Rails (Q i).h k u₀ e}
local notation "C" => Credit.leanC

open WilsonCoeffUV.Cosmos.Polestar
open WilsonSeparatedPrefixMovingReportedLanes (Courts row amount)
open WilsonSeparatedPrefixMovingReportedStableEdge (tuition)
open WilsonSeparatedPrefixMovingReportedStableLaw (reading)
open WilsonIndependentMatchedPhysicalSector (stamp)
open WilsonIndependentMovingRosterAllFineSeats (Elected)
open WilsonSeparatedPrefixMovingCalendar (epoch)
local notation "I" => Fin ((n+1)+1)
def sector (V:Realm G (e+1) C)(flag:I→Bool)(X:Courts (H:=H) (Q:=Q) (v:=v))
    (c:∀s,Verse (Q s).F)(φ:Wilt Q)(y:ℝ)(o:CellR)(m K N:ℕ):Era G ℝ:=
  reading V m K N (fun s=>degree (flag s) k (Q s).h) (row flag X c φ y o)

theorem original (M:Master H)(Q:I→SealR G)(v:∀s,Rails (Q s).h k u₀ e)(out gain height seats:ℕ)
    (stage:((n+1)+1)*k ≤ out)(rank:out ≤ capP Q+gain)(room:capP Q+gain ≤ seats)(width:capP Q+gain ≤ u₀)(surplus:2 ≤ gain):
    let b:=capP Q+gain
    ∃primary:I→Credit,∃terminal:(I→Bool)→Credit,∀(V:Realm G (e+1) C)(_sold:Elected M V height seats)
    (X:Courts (H:=H) (v:=v))(m stop K N:ℕ),stamp V X m K N → V.anchor ≤ m → m ≤ stop → stop ≤ K → K ≤ N →
    ∀(φ:Wilt Q)(B:I→ℝ)(y z gap:ℝ)(o:CellR),0<gap → (∀s c,s≠c→ClearDay (φ s) (φ c) gap) →
    (∀s,radiusH (φ s) 1 y ≤ z) → (∀s,Amplitude (φ s) (B s)) →
    ∀(c:∀s,Verse (Q s).F)(flag:I→Bool),
    let A:=amount 0 b primary X c flag
    let Δ:=sector V flag X c φ y o m K N-sector V flag X c φ y o m stop N
    let pay:=2*(terminal flag).buy (epoch V m stop)*(paceT V.draws.S m stop)^gain*tuition out e b gap z A B
    Auth (ranksV flag k (fun s=>(Q s).h)) Δ ∧ Flush e 0 1 Δ pay ∧ ∀q ≤ e,∀ω:Fin 0→YForest G,‖Δ.2 q 0 ω‖ ≤ pay:=by
  intro b
  let d:=fun s:I=>(Q s).h
  let l:=fun (flag:I→Bool) s=>degree (flag s) k (Q s).h
  obtain ⟨primary,course⟩:=WilsonSeparatedPrefixMovingReportedLanes.original H Q v 0 b (by simpa using width)
  choose terminal pay using fun flag=>WilsonSeparatedPrefixMovingReportedStableSum.original (D:=fun s=>(Q s).D)
    G e gain out d (l flag) C C C surplus
  refine ⟨primary,terminal,?_⟩
  intro V sold X m stop K N chart start base house prior φ B y z gap o apart separated caps test c flag A Δ salary
  have fit:∑s,l flag s ≤ out:=by
    refine le_trans ?_ stage
    suffices (∑s,l flag s) ≤ ∑_s:I,k by simpa using this
    apply Finset.sum_le_sum
    intro s _
    cases r:flag s <;> simp [l,r,degree,(v s).hk]
  have paid:=course V X m K N φ B y o chart test c flag
  have cross:=pay flag V (sold.spring out 0 b rank room (Nat.zero_le _))
    (sold.dorm _ 0 (fit.trans (rank.trans room)) (Nat.zero_le _)) m stop K N start base house prior fit φ A B y z gap o
    (fun s=>count (flag s)) (row flag X c φ y o) (fun s=>(paid s).1) test caps apart
    (fun a c neq=>separated a.succ c.succ (fun eq=>neq (Fin.succ_inj.mp eq))) (fun a=>separated a.succ 0 (Fin.succ_ne_zero a))
    (fun s=>(paid s).2)
  exact cross
end YM.Integration.WilsonSeparatedPrefixMovingReportedFaculty
