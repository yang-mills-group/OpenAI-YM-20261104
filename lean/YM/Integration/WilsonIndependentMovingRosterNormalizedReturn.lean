import YM.Integration.WilsonIndependentMovingRosterNormalizedPortfolio
import YM.Integration.WilsonIndependentMovingRosterNormalizedBook

/-! Signed older measurements of the finite moving product on its own submitted complete normalized columns. -/
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedReturn

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
theorem original (topCap:h ≤ k)(out u b:ℕ)(W₀ V₀:Credit):
    ∃C C':Bits (n+1) → Credit,∀(R:Realm G (e+1) E)(X:Fin ((n+1)+1) → CutsP H T p v E W K U)
      (_spring:SpringD R out u b W₀)(_dorm:∀mask,Dormitory R (ranks (choose (n+1) mask) k h) u V₀)
      (older t m N:ℕ)(_away:t ≤ m)(_prev:older ≤ m)(_upper:m ≤ N)(_live:R.anchor ≤ older)
      (col:Fin ((n+1)+1)→Verse F)(a A B:Fin ((n+1)+1) → ℝ)(φ:Fin ((n+1)+1) → Rarity D)(y z gap:ℝ)(o:CellR)(budget:Bits (n+1) → ℝ),
      let zoom:=paceT R.draws.S m t
      let δ:=paceT R.draws.S m N
      let c:=centers y zoom
      let used:=Finset.univ.erase (quiet (n+1))
      1 ≤ zoom  →  0<gap  →  (∀mask,0 ≤ budget mask)  →  (∀mask,ranks (choose (n+1) mask) k h ≤ out)  →  u+b ≤ u₀  → 
      (∀mask,1 ≤ (b:ℝ)-(((n+2)*h:ℕ):ℝ)-(counts (choose (n+1) mask):ℝ)/4)  → 
      (∀s,(X s).vesselsC=R)  →  (∀s,(X s).m=homes t m s)  → 
      (∀s,(X s).N=N)  →  (∀s,(X s).m+(X s).i=N)  → 
      (∀s,Licensed (X s) R (homes t m s) N (a s) (paceT R.draws.S (homes t m s) N) (A s))  → 
      (∀s,Amplitude (φ s) (B s))  →  (∀s,radiusH (φ s) 1 (c s) ≤ z)  → 
      (∀i j:Fin (n+1),i ≠ j → ClearDay (φ i.succ) (φ j.succ) gap)  → 
      (∀i:Fin (n+1),∀p∈tsupport (φ i.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,gap ≤ dist p (zoom • q))  → 
      (∀mask j,m ≤ j → j<N → (C mask).buy (age R m j)*R.cash (priceWG G e out u b E W₀) j*
        ((ll R.draws j).L.val:ℝ)^((n+2)*h+counts (choose (n+1) mask)) ≤ budget mask)  → 
      ∀q ≤ e,∀ω:Fin 0→YForest G,
        let J:=(∑mask∈used,WilsonIndependentMovingRosterNormalizedPortfolio.rate mask R X col A B (C' mask) out u b older m gap z zoom (budget mask))*δ^(1/4:ℝ)
        let rawRow:=(WilsonIndependentMovingRosterNormalizedBook.raw R X a col φ y o t m older N).2 q 0 ω
        let fittedRow:=(WilsonIndependentMovingRosterNormalizedBook.prescribed R X col φ y o t m older N).2 q 0 ω
        ‖rawRow-fittedRow‖ ≤ J ∧ ‖rawRow‖ ≤ ‖fittedRow‖+J:=by
  classical
  obtain ⟨C,C',bought⟩:=WilsonIndependentMovingRosterNormalizedPortfolio.original (H:=H) (T:=T) (p:=p) (v:=v)
    (n:=n) (E:=E) (W:=W) (K:=K) (U:=U) out u b W₀ V₀
  refine ⟨C,C',?_⟩
  intro R X spring dorm older t m N away prev upper live col a A B φ y z gap o budget zoom δ c used
    zoom1 gap0 budget0 cap seats slack same homes' last times lic amp rad inner far funds q hq ω J rawRow fittedRow
  have wage:=bought R X spring dorm older t m N away prev upper live col a A B φ y z gap o budget
    zoom1 gap0 budget0 cap seats slack same homes' last times lic amp rad inner far funds q hq ω
  let read:=WilsonIndependentMatchedCoverSum.scalar (G:=G) q ω
  have eq:=congrArg read (WilsonIndependentMovingRosterNormalizedBook.original R X (prev.trans upper) topCap same last times homes' a col φ y o)
  rw [map_add] at eq
  let sum:=read (∑mask∈used,WilsonIndependentMovingRosterNormalizedPortfolio.returned mask R X col a φ y o t m older N)
  change rawRow=fittedRow+sum at eq
  change ‖sum‖≤J at wage
  refine ⟨?_,?_⟩
  · rw [eq,add_sub_cancel_left]
    exact wage
  · rw [eq]
    exact (norm_add_le _ _).trans (by linarith only [wage])

end YM.Integration.WilsonIndependentMovingRosterNormalizedReturn
