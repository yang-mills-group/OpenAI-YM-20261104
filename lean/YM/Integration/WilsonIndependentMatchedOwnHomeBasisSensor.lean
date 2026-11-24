import YM.Integration.WilsonIndependentMatchedOwnHomeIntegratedMaster
import YM.Integration.WilsonIndependentMatchedOwnHomeForestShell

/-! The physical signed, cell-integrated, normalized joint basis hearing on
the exact near and far charts used by the issued optical high-order estimate. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeBasisSensor
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
open WilsonIndependentMatchedOwnHomeProfile (scaled)
open WilsonIndependentMatchedOwnHomeKShell (rider)
open WilsonMarkedIndependentNormalizedElection (normalized)
open WilsonIndependentSpoutMasterArms (basis)
open WilsonIndependentMatchedOwnHomeIntegratedMaster (entry)
variable {G:Gauge}{H:Hol G}{n e d:ℕ}{W V:Credit}
local notation "C" => Credit.leanC
variable (R:Realm G (e+1) C)(Q:Fin ((n+1)+1)→SealR G)(φ:Wilt Q)(a:∀i,Alma (Q i).F)
local notation "Qₙ" => (Fin.tail Q)
local notation "φₙ" => (Fin.tail φ)
local notation "aₙ" => (Fin.tail a)

theorem original (granted:HorizonP H R W V Q)(Φ:Rarity d)(y:ℝ)(o:CellR)(t m c v K N q:ℕ)(g ρ:ℝ)
    (awake:R.anchor ≤ t)(base:t ≤ m)(cut:m ≤ K)(top:K ≤ N)(old:v ≤ K):
    let T:=paceT R.draws.S m t
    let X:=normalized R.draws R.paid Qₙ (WilsonIndependentSpoutMasterArms.basis Qₙ aₙ) m N
    WilsonPhysicalMarkedDefect.RawBank.cash q g (embed (WilsonIndependentMatchedOwnHomeIntegratedMaster.entry R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) Φ y o t m c v K N ρ))=
      WilsonIndependentMatchedOwnHomeBornRaw.measured R Qₙ (Q 0) φₙ (scaled (φ 0) T (pace_pos ..)) X (rider R (Q 0) N t m (a 0))
        Φ y o t m c v K N q g ρ Fin.elim0:=by
  exact (WilsonIndependentMatchedOwnHomeIntegratedMaster.actual R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) granted Φ y o t m c v K N q g ρ Fin.elim0 (awake.trans (base.trans cut)) old top).trans
    (WilsonIndependentMatchedOwnHomeMeasuredRoster.original R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) Φ y o granted t m c v K N q awake base cut top old g ρ Fin.elim0)

end YM.Integration.WilsonIndependentMatchedOwnHomeBasisSensor
end
