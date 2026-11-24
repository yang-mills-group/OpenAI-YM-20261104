import YM.Integration.WilsonMovingForkSharpGramUnitBox
import YM.Integration.WilsonSeparatedPrefixMovingJetService
import YM.Integration.WilsonSeparatedPrefixMovingJetSwap

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpGramAxisBox
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonSeparatedPrefixMovingJointCell (toll)

open WilsonSeparatedPrefixMovingCellFactor (constant)
open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{H:Hol G}{n e h k D b m N older:ℕ}{C W V:Credit}

open WilsonSeparatedPrefixMovingJetBall (UnitJet)
variable {D j:ℕ}
variable {E:ℕ}
open WilsonMovingForkSharpGramUnitBox (tested bank)
open WilsonSeparatedPrefixMovingJetService (size pilot resized positive)
open WilsonSeparatedPrefixMovingJetPrice (patient)
def eye (i r:ℕ)(leg:Fin r→YForest G):Era G ℝ→ₗ[ℝ]ℝ where
  toFun:=fun B=>B.2 i r leg
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
def read (R:Realm G (e+1) C)(P:Era G (Vote D))(Q:Era G (Vote E))
    (N k j b older i r:ℕ)(leg:Fin r→YForest G)(v:Volume D)(w:Volume E):ℝ:=
  (cruises R.draws R.paid N (k+j) b older (WilsonMovingForkSharpGramUnitBox.tested P Q v w)).2 i r leg
theorem left (R:Realm G (e+1) C){P:Era G (Vote D)}{Q:Era G (Vote E)}(hp:Auth k P)(hq:Auth j Q)
    (ear:older ≤ b)(top:b ≤ N)(i r:ℕ)(leg:Fin r→YForest G)(v:Volume D)(w:Volume E):
    read R P Q N k j b older i r leg v w=size v*read R P Q N k j b older i r leg (pilot v).val w:=by
  let W:=tuftV (ContinuousLinearMap.apply ℝ ℝ w) Q
  have now:Auth j W:=hq.tuft _
  have ev:=(patient R hp now ear top (eye i r leg)).map_smul (size v) (pilot v).val
  rw [resized] at ev
  exact ev
theorem reverse (R:Realm G (e+1) C){P:Era G (Vote D)}{Q:Era G (Vote E)}(hp:Auth k P)(hq:Auth j Q)
    (N b older i r:ℕ)(leg:Fin r→YForest G)(v:Volume D)(w:Volume E):
    read R P Q N k j b older i r leg v w=read R Q P N j k b older i r leg w v:=by
  unfold read WilsonMovingForkSharpGramUnitBox.tested
  rw [Nat.add_comm k j,WilsonSeparatedPrefixMovingJetSwap.original (hp.tuft _) (hq.tuft _)]
theorem original (R:Realm G (e+1) C){P:Era G (Vote D)}{Q:Era G (Vote E)}(hp:Auth k P)(hq:Auth j Q)
    (ear:older ≤ b)(top:b ≤ N)(i r:ℕ)(leg:Fin r→YForest G):
    let K:=‖(cruises R.draws R.paid N (k+j) b older (bank P Q)).2 i r leg‖
    ∀v w,‖read R P Q N k j b older i r leg v w‖ ≤ size v*size w*K:=by
  intro K v w
  have both:read R P Q N k j b older i r leg v w=size v*(size w*read R P Q N k j b older i r leg (pilot v).val (pilot w).val):=by
    rw [left R hp hq ear top i r leg v w,reverse R hp hq N b older i r leg (pilot v).val w,
      left R hq hp ear top i r leg w (pilot v).val,reverse R hq hp N b older i r leg (pilot w).val (pilot v).val]
  rw [both,norm_mul,norm_mul,Real.norm_of_nonneg (positive v).le,Real.norm_of_nonneg (positive w).le, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (WilsonMovingForkSharpGramUnitBox.original R hp hq ear top i r leg (pilot v,pilot w)) (positive w).le) (positive v).le
end YM.Integration.WilsonMovingForkSharpGramAxisBox
