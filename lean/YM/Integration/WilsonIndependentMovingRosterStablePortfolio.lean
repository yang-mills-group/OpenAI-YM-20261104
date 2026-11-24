import YM.Integration.WilsonIndependentMovingRosterStableMask
import YM.Integration.WilsonIndependentMovingRosterTopAtHomes

/-! The older scalar invoice for the complete sum of stable cuts on one dated near and exterior board. -/
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterStablePortfolio

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

lemma gain (j:Bits n)(used:j ≠ quiet n)(δ:ℝ)(dp:0<δ)(small:δ ≤ 1):
    δ^((counts (choose n j):ℝ)/4) ≤ δ^(1/4:ℝ):=by
  obtain ⟨s,hs⟩:=present n j used
  have one:1 ≤ counts (choose n j):=by
    change 1 ≤ ∑i,WilsonIndependentMatchedRosterSlots.count (choose n j i)
    simpa [hs,WilsonIndependentMatchedRosterSlots.count] using
      (Finset.single_le_sum (f:=fun i=>count (choose n j i)) (fun _ _=>Nat.zero_le _) (Finset.mem_univ s))
  apply Real.rpow_le_rpow_of_exponent_ge dp small
  exact div_le_div_of_nonneg_right (by exact_mod_cast one) (by norm_num)

def rate (mask:Bits (n+1))(R:Realm G (e+1) E)(X:Fin ((n+1)+1) → CutsP H T p v E W K U)
    (a A B:Fin ((n+1)+1) → ℝ)(L:Credit)(out u b older m:ℕ)(gap z zoom budget:ℝ):ℝ:=
  let flag:=choose (n+1) mask
  let l:=ranks flag k h
  let Z:=∏s,factor u b z*(B s*wallet (flag s) (X s) (dose (X s) (a s)) (A s) u b)
  L.buy (age R older m)*
    (zoom^(h+u)*((coinMat l e)^(n+1)*Z)+2*(zoom^(h+u+u)*(budget*profiles (n+1) out e u b gap z Z)))

def returned (mask:Bits (n+1))(R:Realm G (e+1) E)(X:Fin ((n+1)+1) → CutsP H T p v E W K U)
    (a:Fin ((n+1)+1) → ℝ)(φ:Fin ((n+1)+1) → Rarity D)(y:ℝ)(o:CellR)(t m older N:ℕ):Era G ℝ:=
  let c:=centers y (paceT R.draws.S m t)
  cruises R.draws R.paid N (ranks (choose (n+1) mask) k h) N older
    (placed (stable X a φ c (fun _=>o)) (fitted R X a φ c (fun _=>o) N) mask)

theorem original (out u b:ℕ)(W₀ V₀:Credit):
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
      ∀q ≤ e,∀ω:Fin 0 → YForest G,‖(∑mask∈used,returned mask R X a φ y o t m older N).2 q 0 ω‖ ≤ 
        (∑mask∈used,rate mask R X a A B (C' mask) out u b older m gap z zoom (budget mask))*δ^(1/4:ℝ):=by
  classical
  choose C C' sold using (fun mask:Bits (n+1)=>
    WilsonIndependentMovingRosterStableMask.original (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W) (K:=K) (U:=U)
      mask out u b W₀ V₀)
  refine ⟨C,C',?_⟩
  intro R X spring dorm older t m N away prev upper live a A B φ y z gap o budget zoom δ c used
    zoom1 gap0 budget0 cap seats slack same homes' last times lic amp rad inner far funds q hq ω
  have dp:0<δ:=div_pos (R.draws.S.a_pos _) (R.draws.S.a_pos _)
  have d1:δ ≤ 1:=pace_le _ upper
  let read:=WilsonIndependentMatchedCoverSum.scalar (G:=G) q ω
  change ‖read (∑mask∈used,returned mask R X a φ y o t m older N)‖ ≤ _
  rw [map_sum,Finset.sum_mul]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro mask used'
  have wage:=(sold mask R X spring (dorm mask) older t m N away prev upper live a A B φ y z gap (budget mask) o
    zoom1 gap0 (budget0 mask) (cap mask) seats (slack mask) same homes' last times lic amp rad inner far
    (funds mask)).2.2 q hq ω
  change ‖read (returned mask R X a φ y o t m older N)‖ ≤ _ at wage
  rw [← mul_assoc] at wage
  let r:=rate mask R X a A B (C' mask) out u b older m gap z zoom (budget mask)
  change ‖read (returned mask R X a φ y o t m older N)‖ ≤ r*δ^((counts (choose (n+1) mask):ℝ)/4) at wage
  have r0:0 ≤ r:=by
    by_contra! bad
    exact (not_lt_of_ge ((norm_nonneg _).trans wage)) (mul_neg_of_neg_of_pos bad (Real.rpow_pos_of_pos dp _))
  exact wage.trans (mul_le_mul_of_nonneg_left (gain mask (Finset.mem_erase.mp used').1 δ dp d1) r0)

end YM.Integration.WilsonIndependentMovingRosterStablePortfolio
