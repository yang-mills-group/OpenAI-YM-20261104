import YM.Integration.WilsonSeparatedPrefixMovingCommonVisits
import YM.Integration.WilsonSeparatedPrefixMovingJetSwap
import YM.Integration.WilsonIndependentMatchedCoverGrade
import YM.WilsonCoeffUV.Emit.ScaleSlots
import YM.Integration.WilsonSeparatedPrefixMovingCenterPrint
import YM.Integration.WilsonIndependentMatchedTotalTop

/-! Every captured basis field paired with a fixed exterior has an exact
older cell-integral reading. The connected near term and all older proper
faces use the original submitted `LodeStar` at each genuine visit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingCaptureCharge
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonSeparatedPrefixMovingJointCell (toll)

open WilsonSeparatedPrefixMovingCellFactor (constant)
open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{H:Hol G}{n e h k D b m N older:ℕ}{C W V:Credit}

theorem inside (P:TowerS G D)(F:Rarity D)(x y:ℝ)(o:CellR)(h:ℕ)(γ:ℝ):
    word (γ • P) F x y o h=γ • word P F x y o h:=by
  have part (s:Cover):shoe (γ • P) F x y s=γ • shoe P F x y s:=by
    unfold shoe
    rw [Wheel.ScaleS.tuftR]
    rfl
  have whole:pupil h (γ • P) F x y=γ • pupil h P F x y:=by
    unfold pupil
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [part,smul_comm]
  unfold word
  rw [whole]
  exact Wheel.ScaleS.tuftR _ _ _
theorem original {j:ℕ} (R:Realm G (e+1) C)(P:TowerS G D)(A:Era G ℝ)(hp:Auth k P)(ha:Auth j A)
    (ear:older≤b)(top:b≤N)(K:ℕ)(hike:k≤K)(F:Rarity D)(x y:ℝ)(o:CellR)(h:ℕ)(γ:ℝ):
    cruises R.draws R.paid N (K+j) b older (agateV (word (γ • P) F x y o h) A)=
      γ • cruises R.draws R.paid N (j+k) b older (agateV A (word P F x y o h)):=by
  let B:=word P F x y o h
  have hb:Auth k B:=(placed h F (Auth_on hp) x y).tuft _
  rw [inside]
  change cruises R.draws R.paid N (K+j) b older (agateV (γ • B) A)=_
  rw [WilsonSeparatedPrefixMovingJetSwap.original (hb.μ γ) ha,WilsonSeparatedPrefixMovingFixedCapture.scaled]
  have rank:j+k≤K+j:=by omega
  have funded:=ha.manor hb
  rw [WilsonSeparatedPrefixMovingFixedCapture.settled R (funded.tall rank) γ ear top]
  rw [←WilsonIndependentMatchedCoverGrade.carried R.draws R.paid R.hG R.green ear top _ funded rank]
end YM.Integration.WilsonSeparatedPrefixMovingCaptureCharge
