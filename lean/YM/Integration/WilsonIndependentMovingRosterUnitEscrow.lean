import YM.Integration.WilsonIndependentMovingRosterNormalizedMask
import YM.Integration.WilsonIndependentMovingRosterNormalizedEarnings

/-! The complete older response of each individual stable or fitted choice on the funded two-home course. -/
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterUnitEscrow

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterTariff (factor)
open WilsonIndependentMovingRosterStableSale (homes centers)
open WilsonIndependentMovingRosterLaneFilm (Licensed)
open WilsonIndependentMatchedRosterPowers (profiles)
open WilsonIndependentMatchedRosterSlots (degree count entry wallet)
open WilsonIndependentMatchedRosterMasks (Bits choose placed)
open WilsonIndependentMatchedRosterCuts (counts ranks)
open WilsonIndependentMovingRosterTopFields (stable fitted)
open WilsonIndependentMatchedFittedSeat (dose)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedRosterMasks (quiet present)
open WilsonIndependentMatchedCoverDate (age)
variable {G:Gauge}{H:Hol G}{n e h D k u₀:ℕ}{F:Labels.Frame G h}{T:SectionData F}
    {p:h<D}{v:Rails h k u₀ e}{E W K U:Credit}

open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMovingRosterCut (parcel residual)
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonIndependentMovingRosterTopFields (offered)
open WilsonIndependentMovingRosterNormalizedPortfolio (rate returned)
open WilsonIndependentMovingRosterNormalizedEarnings (edge contract booked wealth maximum)
theorem original (out u b:ℕ)(W₀ V₀:Credit):
    ∃C C':Bits (n+1) → Credit,∀(R:Realm G (e+1) E)(X:Fin ((n+1)+1) → CutsP H T p v E W K U)
      (_spring:SpringD R out u b W₀)(_dorm:∀mask,Dormitory R (ranks (choose (n+1) mask) k h) u V₀)
      (older t m N:ℕ)(_away:t ≤ m)(_prev:older ≤ m)(_upper:m ≤ N)(_live:R.anchor ≤ older)
      (col:Fin ((n+1)+1)→Verse F)(a A B:Fin ((n+1)+1) → ℝ)(φ:Fin ((n+1)+1) → Rarity D)(y z gap:ℝ)(o:CellR)(η:ℝ)(fee:Fin ((n+1)+1)→ℝ),
      let zoom:=paceT R.draws.S m t
      let δ:=paceT R.draws.S m N
      let c:=centers y zoom
      1 ≤ zoom  →  0<gap  →  (∀mask,ranks (choose (n+1) mask) k h ≤ out)  →  u+b ≤ u₀  → 
      (∀mask,1 ≤ (b:ℝ)-(((n+2)*h:ℕ):ℝ)-(counts (choose (n+1) mask):ℝ)/4)  → 
      (∀s,(X s).vesselsC=R)  →  (∀s,(X s).m=homes t m s)  → 
      (∀s,(X s).N=N)  →  (∀s,(X s).m+(X s).i=N)  → 
      (∀s,Licensed (X s) R (homes t m s) N (a s) (paceT R.draws.S (homes t m s) N) (A s))  → 
      (∀s,Amplitude (φ s) (B s))  →  (∀s,radiusH (φ s) 1 (c s) ≤ z)  → 
      (∀i j:Fin (n+1),i ≠ j → ClearDay (φ i.succ) (φ j.succ) gap)  → 
      (∀i:Fin (n+1),∀p∈tsupport (φ i.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,gap ≤ dist p (zoom • q))  → 
      (∀mask j,m ≤ j → j ≤ N →
        (C' mask).buy (age R older m)*WilsonIndependentMovingRosterNormalizedEarnings.edge R
          (C mask) (priceWG G e out u b E W₀) ((n+2)*h+counts (choose (n+1) mask)) m j*
          (∏s,wallet (choose (n+1) mask s) (X s) (col s) (A s) u b) ≤
            δ^(-η)*(∏s,if choose (n+1) mask s then fee s else WilsonIndependentMatchedProxyIncome.cost e (col s))) →
      ∀mask:Bits (n+1),
        let flag:=choose (n+1) mask
        let J:=contract n k out e u b h mask gap z zoom B*
          (∏s,if flag s then fee s else WilsonIndependentMatchedProxyIncome.cost e (col s))*
          δ^((counts flag:ℝ)/4-η)
        let seen:=returned mask R X col a φ y o t m older N
        Auth (ranks flag k h) seen ∧ ∀q ≤ e,∀ω:Fin 0→YForest G, ‖seen.2 q 0 ω‖ ≤ J:=by
  classical
  choose C C' allowance using (fun mask:Bits (n+1)=>WilsonIndependentMovingRosterNormalizedMask.original
    (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W) (K:=K) (U:=U) mask out u b W₀ V₀)
  refine ⟨C,C',?_⟩
  intro R X spring dorm older t m N away prev upper live col a A B φ y z gap o η fee zoom δ c
    zoom1 gap0 cap room slack same starts last times lic amp rad inner far funds mask flag J seen
  let dayFee:=fun j:ℕ=>edge R (C mask) (priceWG G e out u b E W₀) ((n+2)*h+counts flag) m j
  obtain ⟨j,head,tail,best⟩:=maximum dayFee upper
  let budget:=dayFee j
  have green:1 ≤ budget:=wealth R _ _ _ (live.trans prev) head
  have passage:=allowance mask R X spring (dorm mask) older t m N away prev upper live col a A B φ y z gap budget o
    zoom1 gap0 (zero_le_one.trans green) (cap mask) room (slack mask) same starts last times lic amp rad inner far
    (fun l ml lN=>best l ml lN.le)
  refine ⟨passage.1,?_⟩
  intro q hq ω
  let pay:=∏s,if flag s then fee s else WilsonIndependentMatchedProxyIncome.cost e (col s)
  let lease:=rate mask R X col A B (C' mask) out u b older m gap z zoom budget
  let house:=contract n k out e u b h mask gap z zoom B
  have oldTime:1 ≤ WilsonIndependentMatchedCoverDate.age R older m:=by
    have land:=R.depth older live
    have seq:=scales R.draws.S prev
    have dt:0≤((m-older:ℕ):ℝ):=by positivity
    unfold WilsonIndependentMatchedCoverDate.age
    linarith
  have z0:0 ≤ z:=(zero_le_one.trans (fieldCap (φ 0) 1 (c 0))).trans (rad 0)
  have gain:lease ≤ house*(δ^(-η)*pay):=booked mask R X col A B (C' mask) out u b older m gap z zoom budget _
    z0 gap0 (zero_le_one.trans zoom1) (fun s=>(amp s).1)
    (fun s=>(lic s (flag s) (col s) (φ s) (c s) z o (B s) (amp s) (rad s) u b room).1)
    ((C' mask).purchase oldTime) green (funds mask j head tail)
  have paid:=passage.2.2 q hq ω
  have low:‖seen.2 q 0 ω‖ ≤ lease*δ^((counts flag:ℝ)/4):=by
    change ‖seen.2 q 0 ω‖ ≤ _ at paid
    unfold lease rate
    rwa [mul_assoc]
  have dp:0 < δ:=pace_pos ..
  have fit:δ^(-η)*δ^((counts flag:ℝ)/4)=δ^((counts flag:ℝ)/4-η):=by
    rw [←Real.rpow_add dp]
    congr 1
    ring
  calc
    ‖seen.2 q 0 ω‖ ≤ _:=low
    _ ≤ house*(δ^(-η)*pay)*δ^((counts flag:ℝ)/4):=mul_le_mul_of_nonneg_right gain (Real.rpow_nonneg dp.le _)
    _ = J:=by change _=house*pay*δ^((counts flag:ℝ)/4-η);rw [←fit];ring

end YM.Integration.WilsonIndependentMovingRosterUnitEscrow
