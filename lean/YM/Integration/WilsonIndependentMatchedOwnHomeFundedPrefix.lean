import YM.Integration.WilsonSeparatedPrefixMovingPinSuffixFunded
import YM.Integration.WilsonSeparatedPrefixMovingPinSuffixPanel
import YM.Integration.WilsonSeparatedPrefixMovingPinnedPupil

/-! At the nominated physical testing room and the actual K in the older
vacuum, withdraw the newly joined far components from the signed raw row. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeFundedPrefix
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Named Elected needed)
open WilsonSeparatedPrefixMovingPinnedRaw (raw)
open WilsonSeparatedPrefixMovingPinnedPupil (Clear)
open WilsonSeparatedPrefixMovingPinChamber (panel)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonIndependentMovingRosterBirthCalendar (room)
open scoped BigOperators Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{n e d height seats:ℕ}

def fare (R:Realm G (e+1) C)(Q:Fin (n+1)→SealR G)(F:SealR G)(X:Herit Q)(Y:F.Rider)
    (first shape chron:Credit)(p m older:ℕ)(width r gap farGap DF:ℝ)(B:Fin (n+1)→ℝ):ℝ:=
  let k:=F.h+capP Q
  let τ:=p+k
  let fresh:=WilsonSeparatedPrefixMovingUnformedSector.invoice Q F X Y e k 0 (capP Q+F.h+(0+τ+2)) r farGap DF B
  let aged:=shape.buy (room r gap width)*WilsonIndependentMovingRosterInvoice.charge Q F X Y e 0 (F.h+(0+τ)) r farGap DF B
  2*fresh*first.buy (epoch R older m)+4*aged*chron.buy (epoch R older m)

theorem original (M:Master H)(Q:Fin (n+1)→SealR G)(F:SealR G)(e p:ℕ)(positive:0<p)
    (near:∀s,Named M height seats (Q s))(far:Named M height seats F)(budget:needed (F.h+capP Q) 0 p ≤ seats):
    ∃first shape chron:Credit,∀(R:Realm G (e+1) C)(_stock:Elected M R height seats)
    (older t b m K N:ℕ),R.anchor ≤ older → older ≤ t → t ≤ b → b ≤ m → m ≤ K → K ≤ N →
    ∀(α:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(r gap farGap DF:ℝ)(B:Fin (n+1)→ℝ)
      (Φ:Rarity d)(y amp:ℝ)(o:CellR)(w:Fin 0→YForest G),
      Clear R Q F α ψ older t b m r gap farGap DF B → Amplitude Φ amp →
    let T:=paceT R.draws.S m t
    let inv:=(5*radiusH Φ (paceT R.draws.S t b) y)^4*amp*
      fare R Q F X Y first shape chron p m older (paceT R.draws.S m b) r gap farGap DF B
    ∀j ≤ e, ‖raw R Q F α ψ X Y Φ y o t m b older N j 0 w-
      panel R Q F α ψ X Y Φ y o t m b older N K j 0 w‖ ≤ (T^p)⁻¹*inv:=by
  obtain ⟨first,shape,chron,earned⟩:=WilsonSeparatedPrefixMovingPinSuffixFunded.original M Q F e p positive near far budget
  refine ⟨first,shape,chron,?_⟩
  intro R stock older t b m K N awake start atFar middle cut top α ψ X Y r gap farGap DF B Φ y amp o w geometry purchased T inv j hj
  obtain ⟨ge,gf,inner,outer,free,place,outside,rad,_,dist⟩:=geometry
  have sep (z:Point4)(hz:z∈tsupport ψ.ψ.val): T*farGap+r ≤ ‖T • z‖:=
    (add_le_add le_rfl (le_max_left r _)).trans (dist z hz)
  let total:=fare R Q F X Y first shape chron p m older (paceT R.draws.S m b) r gap farGap DF B
  have point (z:CellR)(s:Cover):=earned R stock older t b m N K awake start atFar middle cut top α ψ X Y z
    (paceT R.draws.S m b) r gap farGap DF B ge gf inner outer free place outside rad sep s w
  obtain ⟨roster,⟨shoulder⟩⟩:=WilsonIndependentMovingRosterAllFineSeats.roster stock Q F near far
  have old:older ≤ K:=start.trans (atFar.trans (middle.trans cut))
  have born:R.anchor ≤ K:=awake.trans old
  have quote:=WilsonSeparatedPrefixMovingPinSuffixPanel.original R Q F roster shoulder α ψ X Y Φ y o t m b older N K p w
    born old top (pace_le _ atFar) amp total purchased point
  rw [←WilsonSeparatedPrefixMovingPinnedRaw.original R Q F roster shoulder α ψ X Y Φ y o t m b older N j 0 w
    (born.trans top) (old.trans top) (middle.trans (cut.trans top))]
  exact quote.1 j hj
end YM.Integration.WilsonIndependentMatchedOwnHomeFundedPrefix
end
