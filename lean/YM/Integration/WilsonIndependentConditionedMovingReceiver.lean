import YM.Integration.WilsonIndependentMovingRosterStableReceiver
import YM.Integration.WilsonIndependentMovingRosterStableCensus
import YM.Integration.WilsonIndependentMatchedCoverJoined

/-! Propagate the complete arrived field from its marked birth to the genuinely older receiver on the same inherited conditional law. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedMovingReceiver
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical
variable {G:Gauge}{e u:ℕ}

theorem original (G:Gauge)(l e u:ℕ)(E V:Credit):∃C:Credit,
    ∀(R:Realm G (e+1) E)(_later:Dormitory R l u V)(older m birth N:ℕ)(_old:R.anchor ≤ older)
      (_here:older ≤ m)(_top:m ≤ birth)(_quiet:birth ≤ N)(Y:Era G ℝ)(B:ℝ),
      let atM:=cruises R.draws R.paid N l birth m Y
      let atOld:=cruises R.draws R.paid N l birth older Y
      let wage:=C.buy (WilsonIndependentMatchedCoverDate.age R older m)*B
      Auth l atM → Flush e u 1 atM B → Auth l atOld ∧ Flush e u 1 atOld wage ∧
        ∀q≤e,∀ω:Fin 0→YForest G,‖atOld.2 q 0 ω‖≤wage:=by
  obtain ⟨C,stop⟩:=waveSeen G l e u E V
  refine ⟨C,?_⟩
  intro R later older m birth N old here top quiet Y B atM atOld wage head paid
  have smaller:=WilsonIndependentMovingRosterStableReceiver.narrow (pace_pos R.draws.S older m).le (pace_le R.draws.S here) paid
  let debt:=max 0 (R.tempC m m)
  have copy:=stop R later older m (paceT R.draws.S older) m N N B debt
    (WilsonIndependentMatchedCoverDate.age R older m) (pace_escort old here) (PadRank.frugal R old here)
    le_rfl (top.trans quiet) (top.trans quiet) (le_max_right _ _) atM atM (Fringed.same smaller head (le_max_left _ _))
  have same:atOld=cruises R.draws R.paid N l m older atM:=cruisesMore R.draws R.paid Y here top
  have sign:=same ▸ copy.pen
  have real:Flush e u 1 atOld wage:=by
    rw [same]
    exact pace_self R.draws.S older ▸ copy.f_l
  exact ⟨sign,real,fun q hq=>WilsonIndependentMatchedCoverJoined.unit real q hq⟩

end YM.Integration.WilsonIndependentConditionedMovingReceiver
