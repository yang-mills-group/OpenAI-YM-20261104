import YM.Integration.WilsonSeparatedPrefixMovingJetBall
import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
import YM.Integration.WilsonSeparatedPrefixMovingCenterPrint
import YM.Integration.WilsonIndependentMatchedTotalTop

/-! Every captured basis field paired with a fixed exterior has an exact
older cell-integral reading. The connected near term and all older proper
faces use the original submitted `LodeStar` at each genuine visit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJetStock
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonSeparatedPrefixMovingJointCell (toll)

open WilsonSeparatedPrefixMovingCellFactor (constant)
open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{H:Hol G}{n e h k D b m N older:ℕ}{C W V:Credit}

open WilsonSeparatedPrefixMovingJetBall (UnitJet register sterling inspect reading)
variable {D j:ℕ}
def argument (P:Era G (Vote D))(B:Era G ℝ)(v:Volume D):Era G ℝ:=
  agateV (tuftV (ContinuousLinearMap.apply ℝ ℝ v) P) B
def stock (P:Era G (Vote D))(B:Era G ℝ):Era G (WilsonSeparatedPrefixMovingJetBall.Bank D):=
  agateV (tuftV (register D) P) (tuftV (sterling D) B)
theorem paid {P:Era G (Vote D)}{B:Era G ℝ}(hp:Auth k P)(hb:Auth j B):Auth (k+j) (stock P B):=
  (hp.tuft _).woadB (hb.tuft _) (fun u:UnitJet D=>inspect u) (fun _ _ hyp=>BoundedContinuousFunction.ext hyp)
theorem spent {P:Era G (Vote D)}{B:Era G ℝ}(hp:Auth k P)(hb:Auth j B)(v:Volume D):Auth (k+j) (argument P B v):=
  (hp.tuft _).manor hb
theorem appointment (P:Era G (Vote D))(B:Era G ℝ)(u:UnitJet D):
    tuftV (reading u) (stock P B)=argument P B u.val:=by
  apply Prod.ext
  · exact funext fun n=>woad_ply _ _ (inspect u)
  · exact woad_ply _ _ (inspect u)
theorem original (R:Realm G (e+1) C){P:Era G (Vote D)}{B:Era G ℝ}(hp:Auth k P)(hb:Auth j B)
    (ear:older≤b)(top:b≤N)(u:UnitJet D):
    tuftV (reading u) (cruises R.draws R.paid N (k+j) b older (stock P B))=
      cruises R.draws R.paid N (k+j) b older (argument P B u.val):=by
  rw [←appointment P B u]
  exact cruiseT (reading u) R.draws ear R.hG R.green top (paid hp hb)
end YM.Integration.WilsonSeparatedPrefixMovingJetStock
