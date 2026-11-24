import YM.Integration.WilsonIndependentMatchedOwnHomeCellRows
import YM.Integration.WilsonIndependentMatchedOwnHomePinnedMaster
import YM.Integration.WilsonIndependentFittedRosterCash

/-! Finite public matrix coefficients multiply the actual pinned smooth
ordinary product before reporting. The empty angular component and every
old deposited field are retained inside the same integration. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeIntegratedMaster
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

theorem rows (fund:HorizonP H R W V Q)(m c old K N:ℕ)(live:R.anchor ≤ K)(ear:old ≤ m)(cut:m ≤ K)(top:K ≤ N)(y:ℝ)(j:ℕ):
    row R Q φ b m c old K N y j=
      ∑a:(∀i,Alma (Q i).F),∑d∈Finset.HasAntidiagonal.antidiagonal j,
        PowerSeries.coeff d.1 (clock A₀ O₀ N m old (∏i,b i (a i))) • row R Q φ (B₀ Q a) m c old K N y d.2:=by
  funext s;ext z
  have present (v:Herit Q)(k:ℕ):row R Q φ v m c old K N y k s z=PowerSeries.coeff k (point R Q φ v m c old K N y z s):=by
    rw [WilsonIndependentMatchedOwnHomeCellRows.placed R Q φ v fund m c old K N live (ear.trans cut) top y k s z Fin.elim0]
    simp only [WilsonIndependentMatchedOwnHomePinnedMaster.point,WilsonIndependentSpoutScalarLedger.ground,WilsonOlderFreshSoftSocketKinetic.reading,coeff_mk]
  rw [present]
  simp only [Finset.sum_apply,ContinuousMap.sum_apply,Pi.smul_apply,ContinuousMap.smul_apply,smul_eq_mul,present]
  have grant:=congrArg (PowerSeries.coeff j) (WilsonIndependentMatchedOwnHomePinnedMaster.paid R Q φ b fund m c old K N live ear cut top y z s)
  simpa only [map_sum,PowerSeries.coeff_mul] using grant

def entry (Φ:Rarity d)(y:ℝ)(o:CellR)(t m c old K N:ℕ)(ρ:ℝ):Cost:=
  report A₀ O₀ N m old (PowerSeries.C (ρ^4)*recorded R Q φ b Φ y o t m c old K N)

theorem integrated (fund:HorizonP H R W V Q)(Φ:Rarity d)(y:ℝ)(o:CellR)(t m c old K N:ℕ)
    (live:R.anchor ≤ K)(ear:old ≤ m)(cut:m ≤ K)(top:K ≤ N):
    recorded R Q φ b Φ y o t m c old K N=
      ∑a:(∀i,Alma (Q i).F),clock A₀ O₀ N m old (∏i,b i (a i))*
        recorded R Q φ (B₀ Q a) Φ y o t m c old K N:=by
  ext j
  simp only [recorded,coeff_mk,map_sum,PowerSeries.coeff_mul]
  rw [rows R Q φ b fund m c old K N live ear cut top]
  simp only [map_sum,map_smul,smul_eq_mul]

theorem original (fund:HorizonP H R W V Q)(Φ:Rarity d)(y:ℝ)(o:CellR)(t m c old K N:ℕ)(ρ:ℝ)
    (live:R.anchor ≤ K)(ear:old ≤ m)(cut:m ≤ K)(top:K ≤ N):
    entry R Q φ b Φ y o t m c old K N ρ=
      roster (J:=fun i=>Alma (Q i).F) b (fun a=>entry R Q φ (B₀ Q a) Φ y o t m c old K N ρ):=by
  let P:=PowerSeries.C (ρ^4)
  let T:=reel (relativeC A₀ O₀ N old (m-old))
  let u (a:∀i,Alma (Q i).F):=∏i,b i (a i)
  let Z (a:∀i,Alma (Q i).F):=recorded R Q φ (B₀ Q a) Φ y o t m c old K N
  change T (P*recorded R Q φ b Φ y o t m c old K N)=_
  rw [integrated R Q φ b fund Φ y o t m c old K N live ear cut top,Finset.mul_sum,map_sum]
  unfold roster
  apply Finset.sum_congr (by ext;simp)
  intro a _
  change T (P*(clock A₀ O₀ N m old (u a)*Z a))=u a*T (P*Z a)
  have same:T (clock A₀ O₀ N m old (u a))=u a:=
    WilsonIndependentSpoutMasterReport.cancellation A₀ O₀ R.hG R.green m N old ear (cut.trans top) _
  rw [map_mul,map_mul,map_mul,same];ring

theorem actual (Q:Fin ((n+1)+1)→SealR G)(φ:Wilt Q)(b:Herit Q)(fund:HorizonP H R W V Q)
    (Φ:Rarity d)(y:ℝ)(o:CellR)(t m c old K N q:ℕ)(g ρ:ℝ)(w:Fin 0→YForest G)(live:R.anchor ≤ K)(ear:old ≤ K)(top:K ≤ N):
    cash q g (embed (entry R Q φ b Φ y o t m c old K N ρ))=
      WilsonIndependentMatchedOwnHomeMeasuredRoster.reported R Q φ b Φ y o t m c old K N q g ρ w:=by
  unfold entry WilsonIndependentMatchedOwnHomeMeasuredRoster.reported WilsonIndependentMatchedOwnHomeReportedShell.reading
  apply congrArg (fun x:Cost=>cash q g (embed (report A₀ O₀ N m old x)))
  ext j
  rw [coeff_C_mul,coeff_mk,WilsonIndependentMatchedOwnHomeCellRows.coefficient R Q φ b fund Φ y o t m c old K N j live ear top w]

end YM.Integration.WilsonIndependentMatchedOwnHomeIntegratedMaster
end
