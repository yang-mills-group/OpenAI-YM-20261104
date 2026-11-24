import YM.Integration.WilsonMovingForkSharpGramUnitBox
import YM.Integration.WilsonSeparatedPrefixMovingJetOffice
import YM.Integration.WilsonSeparatedPrefixMovingJetSwap

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpGramGrid
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
open WilsonSeparatedPrefixMovingJointFarBook (abroad)
def deposited (R:Realm G (e+1) C)(N k j b older i r:ℕ)(leg:Fin r→YForest G)(A B:Era G ℝ):ℝ:=
  (cruises R.draws R.paid N (k+j) b older (agateV A B)).2 i r leg
def site (P:TowerS G D)(F:Rarity D)(ε y:ℝ)(o:CellR)(s:Cover):Era G ℝ:=
  tuftV (ContinuousLinearMap.apply ℝ ℝ (wheelC ε y s F.ψ o)) (shifted P s)
theorem represented (P:TowerS G D)(F:Rarity D)(ε y:ℝ)(pos:0<ε)(o:CellR)(S:Finset Cover)
    (contains:VisitsT F ε y o ⊆ S)(h:ℕ):
    word P F ε y o h=∑s∈S,drumB h ε • site P F ε y o s:=by
  rw [word,pupil_eye _ _ _ _ _ _ pos]
  refine Finset.sum_subset contains ?_
  intro s _ gone
  change drumB h ε • locale o (shoe P F ε y s)=0
  rw [singless P ε y s o F pos gone,smul_zero]
theorem first (R:Realm G (e+1) C){P:TowerS G D}{B:Era G ℝ}(hp:Auth k P)(hb:Auth j B)(ear:older ≤ b)(top:b ≤ N)
    (i r:ℕ)(leg:Fin r→YForest G)(F:Rarity D)(ε y:ℝ)(pos:0<ε)(o:CellR)(S:Finset Cover)
    (contains:VisitsT F ε y o ⊆ S)(h:ℕ):
    deposited R N k j b older i r leg (word P F ε y o h) B=
    ∑s∈S,drumB h ε*deposited R N k j b older i r leg (site P F ε y o s) B:=by
  obtain ⟨prior,received,_⟩:=WilsonSeparatedPrefixMovingJetOffice.original R hb ear top (abroad i r leg) hp
    (WilsonSeparatedPrefixMovingJetPrice.cover D i r leg)
  have all:Auth k (word P F ε y o h):=(placed h F (Auth_on hp) ε y).tuft _
  change abroad i r leg (_)=_
  rw [←received _ all,represented P F ε y pos o S contains h,map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul,received (site P F ε y o s) ((hp.shifted s).tuft _)]
  rfl
theorem commute (R:Realm G (e+1) C){A B:Era G ℝ}(ha:Auth k A)(hb:Auth j B)(N b older i r:ℕ)(leg:Fin r→YForest G):
    deposited R N k j b older i r leg A B=deposited R N j k b older i r leg B A:=by
  unfold deposited
  rw [Nat.add_comm k j,WilsonSeparatedPrefixMovingJetSwap.original ha hb]
theorem original (R:Realm G (e+1) C){P:TowerS G D}{Q:TowerS G E}(hp:Auth k P)(hq:Auth j Q)
    (ear:older ≤ b)(top:b ≤ N)(i r:ℕ)(leg:Fin r→YForest G)(F:Rarity D)(V:Rarity E)
    (ε y υ z:ℝ)(pos:0<ε)(hυ:0<υ)(o p:CellR)(S T:Finset Cover)
    (ins:VisitsT F ε y o ⊆ S)(int:VisitsT V υ z p ⊆ T)(h h':ℕ):
    deposited R N k j b older i r leg (word P F ε y o h) (word Q V υ z p h')=
    ∑s∈S,drumB h ε*∑t∈T,drumB h' υ*deposited R N k j b older i r leg (site P F ε y o s) (site Q V υ z p t):=by
  have qa:Auth j (word Q V υ z p h'):=(placed h' V (Auth_on hq) υ z).tuft _
  rw [first R hp qa ear top i r leg F ε y pos o S ins h]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  have pa:Auth k (site P F ε y o s):=(hp.shifted s).tuft _
  rw [commute R pa qa,first R hq pa ear top i r leg V υ z hυ p T int h']
  apply Finset.sum_congr rfl
  intro t _
  have qa':Auth j (site Q V υ z p t):=(hq.shifted t).tuft _
  exact congrArg (fun a=>drumB h' υ*a) (commute R qa' pa N b older i r leg)
end YM.Integration.WilsonMovingForkSharpGramGrid
