import YM.Integration.WilsonIndependentMovingRosterStableCensus
import YM.Integration.WilsonIndependentMatchedCoverJoined

/-! Carry the whole stable-mask product to the very same earlier receiver
as the fitted first connection, including its finite scalar. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterStableReceiver
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical
variable {G:Gauge}{e u:ℕ}

theorem narrow {x B:ℝ}{Y:Era G ℝ}(px:0≤x)(fit:x≤1)(paid:Flush e u 1 Y B):Flush e u x Y B:=by
  refine ⟨paid.1,?_⟩
  intro q hq k hk
  apply budget_minor (paid.2 q hq k hk) (fun b=>mul_nonneg (hedge_nn px _) (norm_nonneg _))
  intro b
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold hedge autumn
  apply pow_le_pow_left₀ (by positivity)
  have nonneg:0≤(tread Bank.terrain 0 b:ℝ):=by positivity
  linarith only [mul_le_mul_of_nonneg_right fit nonneg]

theorem original (G:Gauge)(l e u:ℕ)(E V:Credit):∃C:Credit,
    ∀(R:Realm G (e+1) E)(_later:Dormitory R l u V)(older m N:ℕ)(_old:R.anchor ≤ older)
      (_here:older ≤ m)(_top:m ≤ N)(Y:Era G ℝ)(B:ℝ),
      let atM:=cruises R.draws R.paid N l N m Y
      let atOld:=cruises R.draws R.paid N l N older Y
      let wage:=C.buy (WilsonIndependentMatchedCoverDate.age R older m)*B
      Auth l atM → Flush e u 1 atM B → Auth l atOld ∧ Flush e u 1 atOld wage ∧
        ∀q≤e,∀ω:Fin 0→YForest G,‖atOld.2 q 0 ω‖≤wage:=by
  obtain ⟨C,stop⟩:=waveSeen G l e u E V
  refine ⟨C,?_⟩
  intro R later older m N old here top Y B atM atOld wage head paid
  have smaller:=narrow (pace_pos R.draws.S older m).le (pace_le R.draws.S here) paid
  let debt:=max 0 (R.tempC m m)
  have copy:=stop R later older m (paceT R.draws.S older) m N N B debt
    (WilsonIndependentMatchedCoverDate.age R older m) (pace_escort old here) (PadRank.frugal R old here)
    le_rfl top top (le_max_right _ _) atM atM (Fringed.same smaller head (le_max_left _ _))
  have same:atOld=cruises R.draws R.paid N l m older atM:=cruisesMore R.draws R.paid Y here top
  have sign:=same ▸ copy.pen
  have real:Flush e u 1 atOld wage:=by
    rw [same]
    exact pace_self R.draws.S older ▸ copy.f_l
  exact ⟨sign,real,fun q hq=>WilsonIndependentMatchedCoverJoined.unit real q hq⟩

end YM.Integration.WilsonIndependentMovingRosterStableReceiver
