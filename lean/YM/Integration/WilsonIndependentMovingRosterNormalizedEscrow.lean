import YM.Integration.WilsonIndependentMovingRosterNormalizedReturn
import YM.Integration.WilsonIndependentMovingRosterNormalizedEarnings

/-! Spend the dated enrollment on each whole normalized input, with a single optical loss for every mask. -/
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedEscrow

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
open WilsonIndependentMovingRosterStablePortfolio (rate returned)
open WilsonIndependentMovingRosterNormalizedEarnings (edge contract booked wealth maximum)
theorem original (topCap:h ≤ k)(out u b:ℕ)(W₀ V₀:Credit):
    ∃C C':Bits (n+1) → Credit,∀(R:Realm G (e+1) E)(X:Fin ((n+1)+1) → CutsP H T p v E W K U)
      (_spring:SpringD R out u b W₀)(_dorm:∀mask,Dormitory R (ranks (choose (n+1) mask) k h) u V₀)
      (older t m N:ℕ)(_away:t ≤ m)(_prev:older ≤ m)(_upper:m ≤ N)(_live:R.anchor ≤ older)
      (col:Fin ((n+1)+1)→Verse F)(a A B:Fin ((n+1)+1) → ℝ)(φ:Fin ((n+1)+1) → Rarity D)(y z gap:ℝ)(o:CellR)(η:ℝ)(fee:Fin ((n+1)+1)→ℝ),
      let zoom:=paceT R.draws.S m t
      let δ:=paceT R.draws.S m N
      let c:=centers y zoom
      let used:=Finset.univ.erase (quiet (n+1))
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
      ∀q ≤ e,∀ω:Fin 0→YForest G,
        let J:=(∑mask∈used,WilsonIndependentMovingRosterNormalizedEarnings.contract n k out e u b h mask gap z zoom B*
          (∏s,if choose (n+1) mask s then fee s else WilsonIndependentMatchedProxyIncome.cost e (col s)))*δ^(1/4-η:ℝ)
        let rawRow:=(WilsonIndependentMovingRosterNormalizedBook.raw R X a col φ y o t m older N).2 q 0 ω
        let fittedRow:=(WilsonIndependentMovingRosterNormalizedBook.prescribed R X col φ y o t m older N).2 q 0 ω
        ‖rawRow-fittedRow‖ ≤ J ∧ ‖rawRow‖ ≤ ‖fittedRow‖+J:=by
  classical
  obtain ⟨C,C',bought⟩:=WilsonIndependentMovingRosterNormalizedReturn.original (H:=H) (T:=T) (p:=p) (v:=v) (n:=n)
    (E:=E) (W:=W) (K:=K) (U:=U) topCap out u b W₀ V₀
  refine ⟨C,C',?_⟩
  intro R X spring dorm older t m N away prev upper live col a A B φ y z gap o η fee zoom δ c used
    zoom1 gap0 cap seats slack same homes' last times lic amp rad inner far funds q hq ω J rawRow fittedRow
  let edgeFee:=fun (mask:Bits (n+1)) (j:ℕ)=>edge R (C mask) (priceWG G e out u b E W₀)
    ((n+2)*h+counts (choose (n+1) mask)) m j
  choose day head tail best using (fun mask=>WilsonIndependentMovingRosterNormalizedEarnings.maximum (edgeFee mask) upper)
  let budget:=fun mask=>edgeFee mask (day mask)
  have paid1 (mask):1 ≤ budget mask:=wealth R _ _ _ (live.trans prev) (head mask)
  have all:=bought R X spring dorm older t m N away prev upper live col a A B φ y z gap o budget zoom1 gap0
    (fun mask=>zero_le_one.trans (paid1 mask)) cap seats slack same homes' last times lic amp rad inner far
    (fun mask j hj hn=>best mask j hj hn.le) q hq ω
  let payload:=fun mask:Bits (n+1)=>∏s,if choose (n+1) mask s then fee s else WilsonIndependentMatchedProxyIncome.cost e (col s)
  let lease:=fun mask=>WilsonIndependentMovingRosterNormalizedPortfolio.rate mask R X col A B (C' mask)
    out u b older m gap z zoom (budget mask)
  let house:=fun mask=>contract n k out e u b h mask gap z zoom B
  have oldTime:1 ≤ WilsonIndependentMatchedCoverDate.age R older m:=by
    have land:=R.depth older live
    have seq:=scales R.draws.S prev
    have dt:0≤((m-older:ℕ):ℝ):=by positivity
    unfold WilsonIndependentMatchedCoverDate.age
    linarith
  have z0:0 ≤ z:=(zero_le_one.trans (fieldCap (φ 0) 1 (c 0))).trans (rad 0)
  have gain (mask):lease mask ≤ house mask*(δ^(-η)*payload mask):=by
    have pos s:= (lic s (choose (n+1) mask s) (col s) (φ s) (c s) z o (B s) (amp s) (rad s) u b seats).1
    exact booked mask R X col A B (C' mask) out u b older m gap z zoom (budget mask) _ z0 gap0
      (zero_le_one.trans zoom1) (fun s=>(amp s).1) pos ((C' mask).purchase oldTime) (paid1 mask)
      (funds mask (day mask) (head mask) (tail mask))
  have dp:0<δ:=pace_pos ..
  have power:δ^(-η)*δ^(1/4:ℝ)=δ^(1/4-η:ℝ):=by
    rw [← Real.rpow_add dp]
    congr 1
    ring
  have covered:(∑j∈used,lease j)*δ^(1/4:ℝ) ≤ J:=by
    change _ ≤ (∑j∈used,house j*payload j)*δ^(1/4-η:ℝ)
    rw [Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro mask _
    calc
      _ ≤ (house mask*(δ^(-η)*payload mask))*δ^(1/4:ℝ):=
        mul_le_mul_of_nonneg_right (gain mask) (Real.rpow_nonneg dp.le _)
      _ = _:=by rw [←power];ring
  exact ⟨all.1.trans covered,all.2.trans (by linarith only [covered])⟩

end YM.Integration.WilsonIndependentMovingRosterNormalizedEscrow
