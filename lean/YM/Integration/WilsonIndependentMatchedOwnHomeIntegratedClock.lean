import YM.Integration.WilsonIndependentMatchedOwnHomeIntegratedMaster
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeIntegratedClock
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer.Patrol
open WilsonIndependentMatchedOwnHomePinnedMaster (point)
open WilsonIndependentMatchedOwnHomeCellRows (row recorded collect)
open WilsonIndependentSpoutMasterReport (report)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonIndependentFittedRosterCash (roster numerical reserve)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open scoped BigOperators Classical
variable {G:Gauge}{H:Hol G}{n e d:ℕ}{E W V:Credit}
variable (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(b:Herit Q)
local notation "A₀" => R.draws
local notation "O₀" => R.paid
local notation "B₀" => WilsonIndependentSpoutMasterArms.basis

open WilsonIndependentMatchedOwnHomeCellRows (collect)
open WilsonIndependentMatchedOwnHomeIntegratedMaster (entry)

def chart (m v N j:ℕ)(y:ℝ)(c K:ℕ):Cover→Lounge:=
  ∑l∈Finset.range (j+1),PowerSeries.coeff (j-l) ((relativeC A₀ O₀ N v (m-v))^l) • row R Q φ b m c v K N y l

theorem plotted (m c old K N j:ℕ)(Φ:Rarity d)(yOut:ℝ)(o:CellR)(t:ℕ)(ρ:ℝ):
    PowerSeries.coeff j (WilsonIndependentMatchedOwnHomeIntegratedMaster.entry R Q φ b Φ yOut o t m c old K N ρ)=
      ρ^4*WilsonIndependentMatchedOwnHomeCellRows.collect Φ (paceT (A₀).S t c) yOut o (chart R Q φ b m old N j (paceT (A₀).S m c) c K):=by
  unfold WilsonIndependentMatchedOwnHomeIntegratedMaster.entry report
  rw [map_mul,reel_C,PowerSeries.coeff_C_mul,reelQuote]
  congr 1
  simp only [recorded,coeff_mk,chart,map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl;intro l _;ring

theorem placed (fund:HorizonP H R W V Q)(m c old K N j:ℕ)(awake:R.anchor ≤ K)(older:old ≤ K)(top:K ≤ N)(y:ℝ)(s:Cover)(o:CellR):
    chart R Q φ b m old N j y c K s o=PowerSeries.coeff j (report A₀ O₀ N m old
      (WilsonIndependentMatchedOwnHomePinnedMaster.point R Q φ b m c old K N y o s)):=by
  unfold chart report
  rw [reelQuote]
  simp only [Finset.sum_apply,ContinuousMap.sum_apply,Pi.smul_apply,ContinuousMap.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl;intro l _
  rw [WilsonIndependentMatchedOwnHomeCellRows.placed R Q φ b fund m c old K N awake older top y l s o Fin.elim0]
  simp only [WilsonIndependentMatchedOwnHomePinnedMaster.point,WilsonIndependentSpoutScalarLedger.ground,WilsonOlderFreshSoftSocketKinetic.reading,coeff_mk]
  ring

end YM.Integration.WilsonIndependentMatchedOwnHomeIntegratedClock
end
