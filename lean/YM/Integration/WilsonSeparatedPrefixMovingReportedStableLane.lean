import YM.Integration.WilsonIndependentMovingRosterLaneEdge
import YM.Integration.WilsonIndependentMatchedRosterDate

/-! A single marked lane read at its absolute date on its own original
reporting mesh. The fresh and received tests spend the same numerical
offer. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingReportedStableLane
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
theorem original (R:Realm G (e+1) E)(l d w home K N j u b:ℕ)(fromHome:home ≤ j)(atEdge:j < K)
    (φ:Rarity D)(y z:ℝ)(o:CellR)(δ A B:ℝ)(P:ℕ→Era G ℝ)(small:0 < δ)(debt:0 ≤ A)
    (test:Amplitude φ B)(field:radiusH φ 1 y ≤ z)
    (funded:Lane R l d home (K-home) N u b φ y o δ ((w:ℝ)/4) A B P):
    OnEdge R l u b home N j φ y o P (offer u b d w z δ (paceT R.draws.S home (j+1)) A B):=by
  let i:=j-home
  let x:=paceT R.draws.S home (j+1)
  let r:=paceT R.draws.S home j
  let pay:=offer u b d w z δ x A B
  have prior:home+i=j:=by dsimp only [i];omega
  have after:home+(i+1)=j+1:=by omega
  have ix:j+1-home=i+1:=by omega
  have work:i<K-home:=by dsimp only [i];omega
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


theorem gross {l d w m K N j u b:ℕ}(R:Realm G (e+1) E)(base:m≤j)(date:j<K)
    (φ:Rarity D)(y z:ℝ)(o:CellR)(A B:ℝ)(P:ℕ→Era G ℝ)(paid:0≤A)(amp:Amplitude φ B)(box:radiusH φ 1 y≤z)
    (lane:Lane R l d m (K-m) N u b φ y o (paceT R.draws.S m K) ((w:ℝ)/4) A B P):
    OnEdge R l u b m N j φ y o P (offer u b d 0 z (paceT R.draws.S m N) (paceT R.draws.S m (j+1)) A B):=by
  let δ:=paceT R.draws.S m K
  let x:=paceT R.draws.S m (j+1)
  have ep:0<δ:=pace_pos ..
  have xp:0<x:=pace_pos ..
  have hit:=original R l d w m K N j u b base date φ y z o δ A B P ep paid amp box lane
  have small:δ≤x:=(div_le_div_iff_of_pos_right (R.draws.S.a_pos _)).2 (R.draws.S.strictAnti.antitone date)
  have tail:(δ/x)^((w:ℝ)/4)≤1:=Real.rpow_le_one (div_nonneg ep.le xp.le) ((div_le_one xp).2 small) (by positivity)
  have z₀:0≤z:=(zero_le_one.trans (fieldCap φ 1 y)).trans box
  have raised:offer u b d w z δ x A B≤offer u b d 0 z (paceT R.draws.S m N) x A B:=by
    simp only [offer,WilsonIndependentMatchedRosterTariff.weight,Nat.cast_zero,zero_div,Real.rpow_zero,mul_one]
    apply mul_le_mul_of_nonneg_left _ (by unfold WilsonIndependentMatchedRosterTariff.factor;positivity)
    exact mul_le_of_le_one_right (by exact mul_nonneg (inv_nonneg.mpr (pow_nonneg xp.le _)) (mul_nonneg amp.1 paid)) tail
  exact ⟨hit.head,⟨hit.input.1,fun a ha r v hv=>(hit.input.2 a ha r v hv).stepX raised ha⟩,hit.law,
    ⟨hit.coarse.1.trans raised,fun a ha r v=>(hit.coarse.2 a ha r v).more raised⟩,hit.absent⟩

end YM.Integration.WilsonSeparatedPrefixMovingReportedStableLane


