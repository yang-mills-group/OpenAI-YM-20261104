import YM.Integration.WilsonIndependentMovingRosterStablePortfolio

/-! All fitted and stable contributions to the measured scalar of the actual moving raw product at an older date. -/
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterRawReturn

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
local notation "Qₙ" => (fun _:Fin (n+1)=>sectionSeal T p)
local notation "Q₀" => sectionSeal T p
local notation "dosesIn" X:max a:max => (fun i:Fin (n+1)=>dose (X (Fin.succ i)) (a (Fin.succ i)))
local notation "doseOut" X:max a:max => dose (X 0) (a 0)
local notation "near" φ:max => (fun i:Fin (n+1)=>φ (Fin.succ i))

def raw (R:Realm G (e+1) E)(X:Fin ((n+1)+1)→CutsP H T p v E W K U)
    (a:Fin ((n+1)+1)→ℝ)(φ:Fin ((n+1)+1)→Rarity D)(y:ℝ)(o:CellR)(t m older N:ℕ):Era G ℝ:=
  let zoom:=paceT R.draws.S m t
  cruises R.draws R.paid N ((n+2)*k) N older (MassP G ℝ (n+1) (offered X a φ (centers y zoom) (fun _=>o)))-
    cruises R.draws R.paid N (h+capP Qₙ) m older
      (agateV (current R Q₀ (φ 0) (doseOut X a) t m N (y/zoom) o)
        (parcel R Qₙ (near φ) (dosesIn X a) o y m m N))

def prescribed (R:Realm G (e+1) E)(X:Fin ((n+1)+1)→CutsP H T p v E W K U)
    (a:Fin ((n+1)+1)→ℝ)(φ:Fin ((n+1)+1)→Rarity D)(y:ℝ)(o:CellR)(t m older N:ℕ):Era G ℝ:=
  residual R Qₙ Q₀ (near φ) (φ 0) (dosesIn X a) (doseOut X a) o y t m older N

theorem exact_return (R:Realm G (e+1) E)(X:Fin ((n+1)+1)→CutsP H T p v E W K U)
    {older t m N:ℕ}(before:older ≤ N)(cap:h ≤ k)(same:∀s,(X s).vesselsC=R)
    (last:∀s,(X s).N=N)(times:∀s,(X s).m+(X s).i=N)(homes':∀s,(X s).m=homes t m s)
    (a:Fin ((n+1)+1)→ℝ)(φ:Fin ((n+1)+1)→Rarity D)(y:ℝ)(o:CellR):
    raw R X a φ y o t m older N=prescribed R X a φ y o t m older N+
      ∑mask∈Finset.univ.erase (quiet (n+1)),returned mask R X a φ y o t m older N:=by
  have q:=WilsonIndependentMovingRosterTopAtHomes.original (d:=fun _=>h) (D:=fun _=>D)
    (u:=fun _=>u₀) (T:=fun _=>T) (p:=fun _=>p) (v:=fun _=>v) R X before
    (fun _=>le_rfl) cap same last times (homes' 0) (fun s=>homes' s.succ) a φ y o
  exact q

theorem original (topCap:h ≤ k) (out u b:ℕ)(W₀ V₀:Credit):
    ∃C C':Bits (n+1) → Credit,∀(R:Realm G (e+1) E)(X:Fin ((n+1)+1) → CutsP H T p v E W K U)
      (_spring:SpringD R out u b W₀)(_dorm:∀mask,Dormitory R (ranks (choose (n+1) mask) k h) u V₀)
      (older t m N:ℕ)(_away:t ≤ m)(_prev:older ≤ m)(_upper:m ≤ N)(_live:R.anchor ≤ older)
      (a A B:Fin ((n+1)+1) → ℝ)(φ:Fin ((n+1)+1) → Rarity D)(y z gap:ℝ)(o:CellR)(budget:Bits (n+1) → ℝ),
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
        let J:=(∑mask∈used,rate mask R X a A B (C' mask) out u b older m gap z zoom (budget mask))*δ^(1/4:ℝ)
        let rawRow:=(raw R X a φ y o t m older N).2 q 0 ω
        let fittedRow:=(prescribed R X a φ y o t m older N).2 q 0 ω
        ‖rawRow-fittedRow‖ ≤ J ∧ ‖rawRow‖ ≤ ‖fittedRow‖+J:=by
  classical
  obtain ⟨C,C',bought⟩:=WilsonIndependentMovingRosterStablePortfolio.original (H:=H) (T:=T) (p:=p) (v:=v)
    (n:=n) (E:=E) (W:=W) (K:=K) (U:=U) out u b W₀ V₀
  refine ⟨C,C',?_⟩
  intro R X spring dorm older t m N away prev upper live a A B φ y z gap o budget zoom δ c used
    zoom1 gap0 budget0 cap seats slack same homes' last times lic amp rad inner far funds q hq ω J rawRow fittedRow
  have wage:=bought R X spring dorm older t m N away prev upper live a A B φ y z gap o budget
    zoom1 gap0 budget0 cap seats slack same homes' last times lic amp rad inner far funds q hq ω
  let read:=WilsonIndependentMatchedCoverSum.scalar (G:=G) q ω
  have eq:=congrArg read (exact_return R X (prev.trans upper) topCap same last times homes' a φ y o)
  rw [map_add] at eq
  let sum:=read (∑mask∈used,returned mask R X a φ y o t m older N)
  change rawRow=fittedRow+sum at eq
  change ‖sum‖≤J at wage
  refine ⟨?_,?_⟩
  · rw [eq,add_sub_cancel_left]
    exact wage
  · rw [eq]
    exact (norm_add_le _ _).trans (by linarith only [wage])

end YM.Integration.WilsonIndependentMovingRosterRawReturn
