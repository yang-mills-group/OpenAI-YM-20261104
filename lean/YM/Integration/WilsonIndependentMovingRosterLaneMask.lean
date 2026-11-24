import YM.Integration.WilsonIndependentMovingRosterLaneFilm
import YM.Integration.WilsonIndependentMovingRosterTopFields

/-! Every finite choice of stable and fitted lanes starts on the actual
upper return used in the ordinary product expansion, including choices
made at different reporting dates and different domiciles. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterLaneMask
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterSlots (degree count wallet entry)
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMovingRosterLaneEdge (OnEdge)
open WilsonIndependentMovingRosterLaneFilm (Licensed)
open WilsonIndependentMovingRosterTopFields (stable fitted)
open WilsonIndependentMatchedFittedSeat (dose)
open scoped BigOperators Topology Classical
variable {I:Type}{G:Gauge}{H:Hol G}{e k:ℕ}{h D u₀:I→ℕ}
    {F:(s:I)→Labels.Frame G (h s)}{T:(s:I)→SectionData (F s)}
    {p:∀s,h s<D s}{v:(s:I)→Rails (h s) k (u₀ s) e}{E W K U:Credit}
    (R:Realm G (e+1) E)(X:(s:I)→CutsP H (T s) (p s) (v s) E W K U)

theorem original {N:ℕ}(home:I→ℕ)(same:∀s,(X s).vesselsC=R)(start:∀s,(X s).m=home s)
    (last:∀s,(X s).N=N)(upper:∀s,(X s).m+(X s).i=N)(flag:I→Bool)
    (a δ A B y z:I→ℝ)(φ:(s:I)→Rarity (D s))(o:I→CellR)
    (sold:∀s,Licensed (X s) R (home s) N (a s) (δ s) (A s))
    (tests:∀s,Amplitude (φ s) (B s))(rad:∀s,radiusH (φ s) 1 (y s) ≤ z s)
    (u b:ℕ)(room:∀s,u+b ≤ u₀ s):∀s,
      let c:=dose (X s) (a s)
      let P:=entry (flag s) (X s) (a s) c (φ s) (y s) (o s)
      let amt:=wallet (flag s) (X s) c (A s) u b
      P (N-home s)=(if flag s then stable X a φ y o s else fitted R X a φ y o N s) ∧
      0 ≤ amt ∧ Lane R (degree (flag s) k (h s)) (h s) (home s) (N-home s) N u b (φ s) (y s) (o s) (δ s)
        ((count (flag s):ℝ)/4) amt (B s) P ∧
        ∀j:ℕ,home s ≤ j → j < N →
          OnEdge R (degree (flag s) k (h s)) u b (home s) N j (φ s) (y s) (o s) P
            (offer u b (h s) (count (flag s)) (z s) (δ s) (paceT R.draws.S (home s) (j+1)) amt (B s)):=by
  intro s c P amt
  refine ⟨?_,sold s (flag s) c (φ s) (y s) (z s) (o s) (B s) (tests s) (rad s) u b (room s)⟩
  have top:N-home s=(X s).i:=by have hs:=start s; have hu:=upper s;omega
  rw [top]
  dsimp only [P,WilsonIndependentMatchedRosterSlots.entry]
  split
  · rfl
  · exact WilsonIndependentMovingRosterTopFields.figure R X same last upper a φ y o s

end YM.Integration.WilsonIndependentMovingRosterLaneMask

