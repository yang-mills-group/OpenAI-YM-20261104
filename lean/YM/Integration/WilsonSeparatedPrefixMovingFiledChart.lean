import YM.Integration.WilsonSeparatedPrefixMovingFiledContrast
import YM.Integration.WilsonIndependentMatchedOwnHomeReportedShell

/-! Return the already integrated true field, its entire old purse, and its
signed birth difference to its original kinetic measurement. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingFiledChart
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
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonIndependentSpoutMasterReport (report)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Classical
open WilsonSeparatedPrefixMovingCorrectedField (field full)
open WilsonIndependentMatchedOwnHomeIntegratedMaster (entry)
open WilsonIndependentSpoutMasterReport (report)
variable {G:Gauge}{H:Hol G}{n e d:ℕ}{W V:Credit}
local notation "C" => Credit.leanC

theorem returned (R:Realm G (e+1) C)(Q:Fin ((n+1)+1) → SealR G)(φ:Wilt Q)(b:Herit Q)
    (fund:HorizonP H R W V Q)(Φ:Rarity d)(y:ℝ)(o:CellR)(t m c u K N:ℕ)(ρ:ℝ)
    (oldEar:u ≤ m)(gate:R.anchor ≤ t)(home:t ≤ m)(cut:m ≤ K)(top:K ≤ N)(ω:Fin 0 → YForest G):
    entry R Q φ b Φ y o t m c u N N ρ-entry R Q φ b Φ y o t m c u K N ρ=
      ∑a:(∀i,Alma (Q i).F),(∏i,b i (a i))*(
        report R.draws R.paid N m u (field R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) .upper Φ y o t m c u K N ρ ω)-
        report R.draws R.paid N m u (field R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) .planted Φ y o t m c u K N ρ ω)):=by
  let τ:=reel (relativeC R.draws R.paid N u (m-u))
  change τ (full R Q φ b Φ y o t m c u N N ρ)-τ (full R Q φ b Φ y o t m c u K N ρ)=_
  rw [←map_sub,WilsonSeparatedPrefixMovingCorrectedField.original R Q φ b fund Φ y o t m c u K N ρ oldEar gate home cut top ω,map_sum]
  apply Finset.sum_congr (by ext;simp);intro a _
  rw [map_mul,map_sub]
  change report R.draws R.paid N m u (clock R.draws R.paid N m u (∏i,b i (a i)))*_ = _
  rw [WilsonIndependentSpoutMasterReport.cancellation R.draws R.paid R.hG R.green m N u oldEar (cut.trans top)];rfl

theorem salary (H:Hol G)(F:SealR G)(e:ℕ)(E W V:Credit):
    ∃A:Credit,∀(R:Realm G (e+1) E)(_fund:PassportC H R F W V)(N m v:ℕ),
    R.anchor ≤ v → v ≤ m → m ≤ N → ∀(P:Cost)(bill:ℝ),(∀i ≤ e,‖coeff i P‖ ≤ bill) →
    ∀j ≤ e,‖coeff j (report R.draws R.paid N m v P)‖ ≤ ((e:ℝ)+1)*A.buy (Compar R.draws.S R.y v m)*bill:=by
  obtain ⟨A,sale⟩:=SeasonC e H F.ans F.path E W V
  refine ⟨A,?_⟩
  intro R fund N m v gate before top P bill paid j hj
  let I:WindowS G (e+1) E:=⟨fund.f.arch.V,v,m-v,N,N,N,fund.tap.trans_le gate,by omega,le_rfl,le_rfl⟩
  let S:CourseS H F.ans F.path e E W V:=⟨fund.f,I,rfl⟩
  have age:S.Age=Compar R.draws.S R.y v m:=by
    change fund.f.arch.V.y v+(fund.f.arch.V.draws.S.scale (v+(m-v))-_)+_=_
    rw [Nat.add_sub_of_le before,fund.depths,fund.lands];rfl
  let Z:=Compar R.draws.S R.y v m
  have warm:1≤Z:=by change 1≤Compar R.draws.S R.y v m;rw [←age];exact I.warm
  have charge:0 ≤ A.buy Z:=zero_le_one.trans (A.purchase warm)
  have clocked (j l:ℕ)(hj:j ≤ e)(hl:l ≤ e):
      ‖PowerSeries.coeff j ((relativeC R.draws R.paid N v (m-v))^l)‖ ≤ A.buy Z:=by
    have quote:=(sale S j l hj hl).main
    rw [age] at quote
    change ‖PowerSeries.coeff j ((relativeC fund.f.arch.V.draws fund.f.arch.V.paid N v (m-v))^l)‖ ≤ _ at quote
    simpa only [fund.lands,fund.modes] using quote
  have positive:0≤bill:=(norm_nonneg _).trans (paid 0 (Nat.zero_le _))
  unfold report
  rw [reelQuote]
  calc
    _ ≤ ∑_l∈Finset.range (j+1),bill*A.buy Z:=by
      apply (norm_sum_le ..).trans
      apply Finset.sum_le_sum;intro l hl
      rw [norm_mul]
      have ld:=Finset.mem_range.mp hl
      exact mul_le_mul (paid l (by omega)) (clocked (j-l) l (by omega) (by omega)) (norm_nonneg _) positive
    _ = ((j:ℝ)+1)*A.buy Z*bill:=by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one];ring
    _ ≤ _:=by gcongr

end YM.Integration.WilsonSeparatedPrefixMovingFiledChart
end
