import YM.Integration.WilsonIndependentMovingRosterNormalizedInputs
import YM.Integration.WilsonIndependentMovingRosterStableReceiver
import YM.Integration.WilsonIndependentMovingRosterLaneMask

/-! The paid numerical reading uses exactly the literal original mask cut
out of the full signed top product at its own earlier receiver. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedMask

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
open WilsonIndependentMovingRosterNormalizedInputs (pupil)
open WilsonIndependentMatchedFittedSeat (dose)
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}{n e h D k u₀:ℕ}{F:Labels.Frame G h}{T:SectionData F}
    {p:h<D}{v:Rails h k u₀ e}{E W K U:Credit}

theorem original (mask:Bits (n+1))(out u b:ℕ)(W₀ V₀:Credit):
    let flag:=choose (n+1) mask
    let l:=ranks flag k h
    ∃C C':Credit,∀(R:Realm G (e+1) E)(X:Fin ((n+1)+1)→CutsP H T p v E W K U)
      (_spring:SpringD R out u b W₀)(_later:Dormitory R l u V₀)
      (older t m N:ℕ)(_away:t ≤ m)(_prev:older ≤ m)(_upper:m ≤ N)(_live:R.anchor ≤ older)
      (col:Fin ((n+1)+1)→Verse F)(a A B:Fin ((n+1)+1)→ℝ)(φ:Fin ((n+1)+1)→Rarity D)(y z gap budget:ℝ)(o:CellR),
      let zoom:=paceT R.draws.S m t
      let δ:=paceT R.draws.S m N
      let c:=centers y zoom
      let amt:=fun s=>wallet (flag s) (X s) (col s) (A s) u b
      let Z:=∏s,factor u b z*(B s*amt s)
      let unitFee:=zoom^(h+u)*((coinMat l e)^(n+1)*Z)
      let joins:=2*(zoom^(h+u+u)*(budget*profiles (n+1) out e u b gap z Z))
      let rent:=C'.buy (WilsonIndependentMatchedCoverDate.age R older m)*((unitFee+joins)*δ^((counts flag:ℝ)/4))
      let Y:=placed (stable X a φ c (fun _=>o)) (pupil R X col φ c (fun _=>o) N) mask
      let seen:=cruises R.draws R.paid N l N older Y
      1≤zoom → 0<gap → 0≤budget → l≤out → u+b≤u₀ →
      1≤(b:ℝ)-(((n+2)*h:ℕ):ℝ)-(counts flag:ℝ)/4 →
      (∀s,(X s).vesselsC=R) → (∀s,(X s).m=homes t m s) →
      (∀s,(X s).N=N) → (∀s,(X s).m+(X s).i=N) →
      (∀s,Licensed (X s) R (homes t m s) N (a s) (paceT R.draws.S (homes t m s) N) (A s)) →
      (∀s,Amplitude (φ s) (B s)) → (∀s,radiusH (φ s) 1 (c s)≤z) →
      (∀i j:Fin (n+1),i≠j→ClearDay (φ i.succ) (φ j.succ) gap) →
      (∀i:Fin (n+1),∀p∈tsupport (φ i.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,gap≤dist p (zoom • q)) →
      (∀j,m≤j→j<N→C.buy (WilsonIndependentMatchedCoverDate.age R m j)*R.cash (priceWG G e out u b E W₀) j*
        ((ll R.draws j).L.val:ℝ)^((n+2)*h+counts flag)≤budget) →
      Auth l seen ∧ Flush e u 1 seen rent ∧ ∀q≤e,∀ω:Fin 0→YForest G,‖seen.2 q 0 ω‖≤rent:=by
  intro flag l
  let ks:=fun s=>degree (flag s) k h
  let ws:=fun s=>count (flag s)
  let ds:=fun _:Fin ((n+1)+1)=>h
  have cnt:(∑s,ws s)=counts flag:=rfl
  have dims:(∑s,ds s)=(n+2)*h:=by simp [ds]
  obtain ⟨C,early⟩:=WilsonIndependentMovingRosterStableCensus.original (D:=fun _=>D) G out e u b ks E W₀ V₀
  obtain ⟨C',late⟩:=WilsonIndependentMovingRosterStableReceiver.original G l e u E V₀
  refine ⟨C,C',?_⟩
  intro R X spring later older t m N away prev upper live col a A B φ y z gap budget o zoom δ c amt Z
    unitFee joins rent Y seen fit apt money capacity moment slack same starts last top sold tests caps close far bank
  let paths:=fun s=>entry (flag s) (X s) (a s) (col s) (φ s) (c s) o
  have posted:=(fun s=>sold s (flag s) (col s) (φ s) (c s) z o (B s) (tests s) (caps s) u b moment)
  have atEnd:(fun s=>paths s (N-homes t m s))=
      fun s=>if flag s then stable X a φ c (fun _=>o) s else pupil R X col φ c (fun _=>o) N s:=by
    funext s
    have idx:N-homes t m s=(X s).i:=by have start:=starts s; have end':=top s;omega
    rw [idx]
    dsimp only [paths,WilsonIndependentMatchedRosterSlots.entry]
    split
    · rfl
    · exact WilsonIndependentMovingRosterNormalizedInputs.figure R X same last top col φ c (fun _=>o) s
  have outer:=early R spring later t m N away upper (live.trans prev) ds ws φ paths amt B y z gap budget o
    fit apt money capacity (by simpa only [dims,cnt] using slack)
    (fun s=>(posted s).1) tests caps close far
    (fun j hj hn=>by simpa only [dims,cnt] using bank j hj hn) (fun s=>(posted s).2.1)
  dsimp only at outer
  rw [atEnd] at outer
  exact late R later older m N live prev upper Y _ outer.1 outer.2

end YM.Integration.WilsonIndependentMovingRosterNormalizedMask
