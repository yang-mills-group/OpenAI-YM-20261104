import YM.Integration.WilsonIndependentMovingRosterLaneEdge
/-! Read a lane up to its marked birth on the inherited vacuum. Numerical records travel with the actual draws and chart ratio. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedMovingLane
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMatchedCoverProfile (Income)
open scoped BigOperators Topology Classical
variable {G:Gauge}{D e:ℕ}{E:Credit}

open WilsonIndependentMovingRosterLaneEdge (OnEdge)

theorem resident (R:Realm G (e+1) E)(l d w u b home j birth N:ℕ)(start:home≤j)(top:j≤birth)
    (φ:Rarity D)(y z:ℝ)(o:CellR)(δ A B:ℝ)(P:ℕ→Era G ℝ)(dp:0<δ)(ap:0≤A)
    (test:Amplitude φ B)(box:radiusH φ 1 y≤z)
    (funded:Lane R l d home (birth-home) N u b φ y o δ ((w:ℝ)/4) A B P):
    let x:=paceT R.draws.S home j
    Auth l (P (j-home)) ∧ Flush e u x (P (j-home)) (offer u b d w z δ x A B):=by
  intro x
  have legal:j-home≤birth-home:=Nat.sub_le_sub_right top home
  have x₀:0<x:=pace_pos ..
  have xc:x≤1:=pace_le _ start
  have box₀:0≤z:=(zero_le_one.trans (fieldCap ..)).trans box
  have heard:=funded.billed (j-home) legal
  rw [Nat.add_sub_of_le start] at heard
  have cost:=WilsonIndependentMatchedRosterTariff.outgoing φ u b d w δ x x y z A B x₀ le_rfl
    dp ap test.1 (WilsonIndependentMatchedRosterDate.radius _ x₀ xc box)
  exact ⟨funded.accounts.head _ legal,WilsonIndependentMatchedRosterTariff.positive _ _ _ _ box₀ dp.le x₀.le ap test.1,
    fun q hq r hr=>(heard.2 q hq r hr).more cost⟩

theorem edge (R:Realm G (e+1) E)(l d w home birth N j u b:ℕ)(fromHome:home ≤ j)(atEdge:j < birth)
    (φ:Rarity D)(y z:ℝ)(o:CellR)(δ A B:ℝ)(P:ℕ→Era G ℝ)(small:0 < δ)(debt:0 ≤ A)
    (test:Amplitude φ B)(field:radiusH φ 1 y ≤ z)
    (funded:Lane R l d home (birth-home) N u b φ y o δ ((w:ℝ)/4) A B P):
    OnEdge R l u b home N j φ y o P (offer u b d w z δ (paceT R.draws.S home (j+1)) A B):=by
  let i:=j-home
  let x:=paceT R.draws.S home (j+1)
  let r:=paceT R.draws.S home j
  let pay:=offer u b d w z δ x A B
  have prior:home+i=j:=by dsimp only [i];omega
  have after:home+(i+1)=j+1:=by omega
  have ix:j+1-home=i+1:=by omega
  have work:i<birth-home:=by dsimp only [i];omega
  have hx:0 < x:=pace_pos ..
  have hr:0 < r:=pace_pos ..
  have xr:x ≤ r:=(div_le_div_iff_of_pos_right (R.draws.S.a_pos _)).2 (R.draws.S.strictAnti.antitone (Nat.le_succ _))
  have fine:x ≤ 1:=pace_le _ (by omega)
  have coarse:r ≤ 1:=pace_le _ fromHome
  have zpos:0 ≤ z:=(zero_le_one.trans (fieldCap φ 1 y)).trans field
  have paid:0 ≤ pay:=WilsonIndependentMatchedRosterTariff.positive _ _ _ _ zpos small.le hx.le debt test.1
  have power:=WilsonIndependentMatchedRosterTariff.incoming φ u b d w δ x y z A B hx small debt test.1
    (WilsonIndependentMatchedRosterDate.radius φ hx fine field)
  have lower:=WilsonIndependentMatchedRosterTariff.outgoing φ u b d w δ x r y z A B hx xr small debt test.1
    (WilsonIndependentMatchedRosterDate.radius φ hr coarse field)
  have original:=funded.accounts.cash i work
  rw [prior,after] at original
  have billed:=funded.billed i work.le
  rw [prior] at billed
  have law:=funded.pushed i work
  rw [prior] at law
  constructor <;> rw [ix]
  · exact funded.accounts.head (i+1) work
  · exact ⟨original.1,fun a ha r v hv=>(original.2 a ha r v hv).stepX power ha⟩
  · exact law
  · rw [law]
    exact ⟨paid,fun a ha r hv=>(billed.2 a ha r hv).more lower⟩
  · have empty:=funded.accounts.empty i work
    simpa only [after] using empty


theorem on_draws {E':Credit}{R:Realm G (e+1) E}{R':Realm G (e+1) E'}
    (files:R.draws=R'.draws)(clock:R.paid=R'.paid)
    {l d m s N u b:ℕ}{φ:Rarity D}{y δ α A B:ℝ}{o:CellR}{P:ℕ→Era G ℝ}
    (bound:Lane R l d m s N u b φ y o δ α A B P):
    Lane R' l d m s N u b φ y o δ α A B P:=by
  refine ⟨⟨bound.accounts.head,?_,?_,bound.accounts.home⟩,?_,?_⟩
  · simpa only [files] using bound.accounts.cash
  · simpa only [files] using bound.accounts.empty
  · simpa only [files] using bound.billed
  · simpa only [files,clock] using bound.pushed

end YM.Integration.WilsonIndependentConditionedMovingLane
