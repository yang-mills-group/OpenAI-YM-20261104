import YM.Integration.WilsonSeparatedPrefixMovingOrdinarySwitch
import YM.Integration.WilsonIndependentMatchedOwnHomeIntegratedMaster

/-! Open the actual fitted moving source *after* integrating the complete joint
row. Its common clock, its three child phases and its unapportioned old vacuum
belong to both cutoffs. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingCorrectedField
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Flooring
open WilsonSeparatedPrefixMovingOrdinarySwitch (Birth tape)
open WilsonIndependentMatchedOwnHomeProfile (scaled)
open WilsonIndependentMatchedOwnHomeCoordinates (brought)
open WilsonIndependentSpoutMasterArms (basis)
open WilsonIndependentMatchedOwnHomeCellRows (recorded)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonMarkedIndependentNormalizedElection (normalized)
open scoped BigOperators Classical
variable {G:Gauge}{H:Hol G}{n e d:ℕ}{W V:Credit}
local notation "C" => Credit.leanC
variable (R:Realm G (e+1) C)(Q:Fin ((n+1)+1) → SealR G)(φ:Wilt Q)(b:Herit Q)
local notation "A" => R.draws
local notation "O₀" => R.paid
local notation "F₀" => Q 0
local notation "Qₙ" => (fun i:Fin (n+1)=>Q (Fin.succ i))
local notation "φₙ" => (fun i:Fin (n+1)=>φ (Fin.succ i))
local notation "bₙ" => (fun i:Fin (n+1)=>b (Fin.succ i))

def full (Φ:Rarity d)(y:ℝ)(o:CellR)(t m c old K N:ℕ)(ρ:ℝ):Cost:=
  PowerSeries.C (ρ^4)*recorded R Q φ b Φ y o t m c old K N

def field (s:Birth)(Φ:Rarity d)(y:ℝ)(o:CellR)(t m c old K N:ℕ)(ρ:ℝ)(ω:Fin 0 → YForest G):Cost:=
  let T:=paceT R.draws.S m t
  WilsonSeparatedPrefixMovingOrdinarySwitch.tape s R Qₙ F₀ φₙ (scaled (φ 0) T (pace_pos ..)) (normalized A O₀ Qₙ bₙ m N)
    (PermuteLens A O₀ F₀ N t (brought A O₀ F₀ N t m (b 0))) Φ y o t m c old K N ρ ω

theorem planted (fund:HorizonP H R W V Q)(Φ:Rarity d)(y:ℝ)(o:CellR)(t m c old K N:ℕ)(ρ:ℝ)
    (gate:R.anchor ≤ t)(own:t ≤ m)(cut:m ≤ K)(top:K ≤ N)(oldEar:old ≤ K)(ω:Fin 0 → YForest G):
    full R Q φ b Φ y o t m c old K N ρ=field R Q φ b .planted Φ y o t m c old K N ρ ω:=by
  ext j
  rw [full,coeff_C_mul,WilsonIndependentMatchedOwnHomeCellRows.coefficient R Q φ b fund Φ y o t m c old K N j
    (gate.trans (own.trans cut)) oldEar top ω]
  rw [WilsonIndependentMatchedOwnHomeMeasuredRoster.placed R Q φ b Φ y o fund t m c old K N j 0 gate own cut top oldEar ω]
  simp only [field,WilsonSeparatedPrefixMovingOrdinarySwitch.tape,coeff_mk];ring

theorem upper (fund:HorizonP H R W V Q)(Φ:Rarity d)(y:ℝ)(o:CellR)(t m c old K N:ℕ)(ρ:ℝ)
    (gate:R.anchor ≤ t)(own:t ≤ m)(cut:m ≤ K)(top:K ≤ N)(oldEar:old ≤ K)(ω:Fin 0 → YForest G):
    full R Q φ b Φ y o t m c old N N ρ=field R Q φ b .upper Φ y o t m c old K N ρ ω:=by
  rw [planted R Q φ b fund Φ y o t m c old N N ρ gate own (cut.trans top) le_rfl (oldEar.trans top) ω]
  ext j
  simp only [field,WilsonSeparatedPrefixMovingOrdinarySwitch.tape,coeff_mk]
  rw [WilsonIndependentMatchedOwnHomeBornRaw.self R Qₙ F₀ φₙ _ _ _ Φ y o (fun i=>fund i.succ) (Classical.choice (fund 0))
    t m c old N j 0 ω (gate.trans (own.trans (cut.trans top))) (oldEar.trans top)]

theorem opened (fund:HorizonP H R W V Q)(Φ:Rarity d)(y:ℝ)(o:CellR)(t m c old K N:ℕ)(ρ:ℝ)
    (oldEar:old ≤ m)(gate:R.anchor ≤ t)(own:t ≤ m)(cut:m ≤ K)(top:K ≤ N):
    full R Q φ b Φ y o t m c old K N ρ=
      ∑a:(∀i,Alma (Q i).F),clock A O₀ N m old (∏i,b i (a i))*full R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) Φ y o t m c old K N ρ:=by
  unfold full
  rw [WilsonIndependentMatchedOwnHomeIntegratedMaster.integrated R Q φ b fund Φ y o t m c old K N
    (gate.trans (own.trans cut)) oldEar cut top,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro a _;ring

theorem original (fund:HorizonP H R W V Q)(Φ:Rarity d)(y:ℝ)(o:CellR)(t m c old K N:ℕ)(ρ:ℝ)
    (oldEar:old ≤ m)(gate:R.anchor ≤ t)(own:t ≤ m)(cut:m ≤ K)(top:K ≤ N)(ω:Fin 0 → YForest G):
    full R Q φ b Φ y o t m c old N N ρ-full R Q φ b Φ y o t m c old K N ρ=
      ∑a:(∀i,Alma (Q i).F),clock A O₀ N m old (∏i,b i (a i))*
        (field R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) .upper Φ y o t m c old K N ρ ω-field R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) .planted Φ y o t m c old K N ρ ω):=by
  rw [opened R Q φ b fund Φ y o t m c old N N ρ oldEar gate own (cut.trans top) le_rfl,
    opened R Q φ b fund Φ y o t m c old K N ρ oldEar gate own cut top,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl;intro a _
  rw [upper R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) fund Φ y o t m c old K N ρ gate own cut top (oldEar.trans cut) ω,
    planted R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) fund Φ y o t m c old K N ρ gate own cut top (oldEar.trans cut) ω,mul_sub]

end YM.Integration.WilsonSeparatedPrefixMovingCorrectedField
end
