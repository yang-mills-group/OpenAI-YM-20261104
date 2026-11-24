import YM.Integration.WilsonIndependentMatchedPhysicalReturn
/-! Whole signed ordinary physical source on the old vacuum against the buffered, refilled row.
Every nonempty stable subset is bought on the same original receiving course. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPhysicalOrdinary
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
variable {G:Gauge}{n k e u₀:ℕ}{H:Hol G}{Q:Fin (n+1)→SealR G}{v:∀i,Rails (Q i).h k u₀ e}
local notation "C" => Credit.leanC
abbrev Courts:=(i:Fin (n+1))→CutsP H (Q i).ans (Q i).path (v i) C C C C

open WilsonIndependentMatchedPhysicalSector (stamp field)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedCoveredSeats (seat traced)
open WilsonIndependentMatchedRosterMasks (Bits quiet choose placed)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonPositionProgramTrialAccrued (home)
open private summed from YM.Integration.WilsonIndependentMatchedRosterPlanted

open WilsonIndependentMatchedPhysicalReturn (ordinary)
open WilsonPositionProgramTrialHomeFaces (Outcome)

def price (V:Realm G (e+1) C)(X:Courts (H:=H) (v:=v))(u b out host m K:ℕ)
    (primary:Fin (n+1)→Credit)(mid last:(Fin (n+1)→Bool)→Credit)(Z:ℝ)(B:Fin (n+1)→ℝ):ℝ:=
  ∑j∈Finset.univ.erase (quiet n),let mask:=choose n j
  WilsonIndependentMatchedPhysicalSector.charge V X mask u b out host m K primary
    (mid mask) (last mask) Z⁻¹ (2*Z+1) B

private theorem more {u:ℕ}{P P':Era G ℝ}{a b:ℝ}
    (h:response e u P a)(h':response e u P' b):response e u (P+P') (a+b):=by
  refine ⟨⟨add_nonneg h.1.1 h'.1.1,?_⟩,?_⟩
  · intro j hj r hr
    exact (h.1.2 j hj r hr).plus (h'.1.2 j hj r hr) zero_le_one
  · intro j hj ctx
    exact (norm_add_le ..).trans (add_le_add (h.2 j hj ctx) (h'.2 j hj ctx))

theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(v:∀i,Rails (Q i).h k u₀ e)(u b out:ℕ)
    (width:u+b ≤ u₀)(stage:(n+1)*k ≤ out)(spread:1 ≤ (b:ℝ)-((∑s,(Q s).h:ℕ):ℝ)-((n+1:ℕ):ℝ)/4):
    ∃(primary:Fin (n+1)→Credit)(middle last:(Fin (n+1)→Bool)→Credit),∀(V:Realm G (e+1) C)
    (X:Courts (H:=H) (v:=v))(host m K N N':ℕ)(B:Fin (n+1)→ℝ)(Z ε:ℝ),stamp V X m K N →
    V.anchor ≤ host → host ≤ m → m ≤ K → K ≤ N → SpringD V out u b C → (∀l ≤ out,Dormitory V l u C) →
    (∀s,On (Q s).h (X s).pt) → 0 ≤ ε →
    Outcome Q V.draws V.paid (fun s=>home (Q s) (X s)) m K N N' host e u B Z ε →
    ∀(F:Wilt Q)(y:ℝ)(o:CellR),Bough Q F y Z B →
    response e u (cruises V.draws V.paid N (capP Q) K host (ordinary V.draws X F m K y o)-
      stopped V.draws V.paid Q F (fun s=>home (Q s) (X s)) m K N' host y o)
      (price V X u b out host m K primary middle last Z B+ε):=by
  obtain ⟨primary,middle,last,sector⟩:=WilsonIndependentMatchedPhysicalSector.original H Q v u b out width stage spread
  refine ⟨primary,middle,last,?_⟩
  intro V X host m K N N' B Z ε filed awake active start live spring dorm good eps matched F y o shape
  have span s:radiusH (F s) 1 y ≤ 2*Z+1:=by
    simp only [radiusH,abs_one]
    linarith only [shape.rents s,shape.room]
  have parts:=sector V X host m K N F B Z⁻¹ (2*Z+1) y o filed awake active start live spring dorm
    (inv_pos.mpr (zero_lt_one.trans_le shape.pos)) shape.seats span shape.lanes
  let src:=cruises V.draws V.paid N (capP Q) K host (ordinary V.draws X F m K y o)
  let old:=stopped V.draws V.paid Q F (fun s=>home (Q s) (X s)) m K N host y o
  let fresh:=stopped V.draws V.paid Q F (fun s=>home (Q s) (X s)) m K N' host y o
  have dirty:response e u (src-old) (price V X u b out host m K primary middle last Z B):=by
    dsimp only [src,old]
    rw [WilsonIndependentMatchedPhysicalReturn.exactRows V X F B host m K N y o filed active start live good shape.lanes]
    apply summed
    intro j _
    exact parts (choose n j)
  have fee:=matched F y o shape
  have transfer:response e u (old-fresh) ε:=by
    exact ⟨⟨eps,fun j hj r _=>fee.1 j r hj⟩,fun j hj t=>fee.2 j hj t⟩
  have total:=more dirty transfer
  rwa [sub_add_sub_cancel] at total

end YM.Integration.WilsonIndependentMatchedPhysicalOrdinary
