import YM.Integration.WilsonIndependentNotebookComplexCorners
import YM.Integration.WilsonIndependentConditionedFolioPupil
import YM.Integration.WilsonIndependentMatchedRosterSigned

/-! A native four-corner cut is a finite hearing of all its two real K-grid visits. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioReader
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentConditionedPairFiledSemester (Tested)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Topology Classical
open Extra.Histories
open WilsonIndependentConditionedBankMatrix (protocol sample)
open WilsonIndependentNotebookComplexQuadrant (axes fuse)
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonIndependentConditionedBankPublicGram (response)
open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedBankCorner (input)
open WilsonIndependentFittedPivotCash (view)
local notation "J" => Fin 2
local notation "C" => Credit.leanC

open WilsonIndependentMatchedTotalTop (binary)
open WilsonIndependentFittedPivotCash (measured)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonIndependentNotebookComplexCorners (reader)
open private summing from YM.Integration.WilsonIndependentMatchedRosterSigned

def ear {G:Gauge}(q:ℕ)(g:ℝ)(z:Fin 0→YForest G):Era G ℝ →+ℂ:=AddMonoidHom.mk'
  (fun X=>measured q g (reading X.2 z)) (fun X Y=>by
    rw [←map_add]
    apply congrArg (measured q g)
    ext n
    simp [WilsonOlderFreshSoftSocketKinetic.reading])

private def left {G:Gauge}(Y:Era G ℝ):Era G ℝ →+Era G ℝ:=AddMonoidHom.mk' (fun X=>agateV X Y)
  (fun A B=>(binary A B Y).1)
private def right {G:Gauge}(X:Era G ℝ):Era G ℝ →+Era G ℝ:=AddMonoidHom.mk' (fun Y=>agateV X Y)
  (fun A B=>(binary A B X).2)

theorem pair {G:Gauge}{e k l m K N:ℕ}{E:Credit}(V:Realm G (e+1) E)(live:m≤K)(top:K≤N)
    {U T:Type*}(s:Finset U)(t:Finset T)(A:U→Era G ℝ)(B:T→Era G ℝ)
    (pa:∀i∈s,Auth k (A i))(pb:∀j∈t,Auth l (B j))(q:ℕ)(g:ℝ)(z:Fin 0→YForest G):
    ear q g z (cruises V.draws V.paid N (k+l) K m (agateV (∑i∈s,A i) (∑j∈t,B j)))=
      ∑i∈s,∑j∈t,ear q g z (cruises V.draws V.paid N (k+l) K m (agateV (A i) (B j))):=by
  classical
  have product:agateV (∑i∈s,A i) (∑j∈t,B j)=∑i∈s,∑j∈t,agateV (A i) (B j):=by
    rw [show agateV (∑i∈s,A i) (∑j∈t,B j)=(left (∑j∈t,B j)) (∑i∈s,A i) from rfl,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact map_sum (right (A i)) .. 
  rw [product,summing (R:=V) live top s _ (fun i hi=>Auth.sum fun j hj=>(pa i hi).manor (pb j hj)),map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [summing (R:=V) live top t _ (fun j hj=>(pa i hi).manor (pb j hj)),map_sum]

def site {G:Gauge}{D:ℕ}(T:TowerS G D)(φ:Rarity D)(x y:ℝ)(o:CellR)(h:ℕ)(n:Lattice.Cover):Era G ℝ:=
  drumB h x •locale o (shoe T φ x y n)

theorem price {G:Gauge}{D k:ℕ}{T:TowerS G D}(p:On k T)(φ:Rarity D)(x y:ℝ)(o:CellR)(h:ℕ)(n:Lattice.Cover):
    Auth k (site T φ x y o h n):=((seaWet _ _ _ _ p n).tuft _).μ _

theorem locations {G:Gauge}{D:ℕ}(T:TowerS G D)(φ:Rarity D)(x y:ℝ)(o:CellR)(h:ℕ):
    WilsonIndependentMatchedCoverProfile.word T φ x y o h=∑n∈canvasM φ x y,site T φ x y o h n:=shoreSum _

end YM.Integration.WilsonIndependentConditionedFolioReader
end
