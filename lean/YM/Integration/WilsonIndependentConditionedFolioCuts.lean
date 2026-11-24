import YM.Integration.WilsonIndependentConditionedFolioReader

/-! The immutable selected cuts read every visited K site on their common inherited N vacuum. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioCuts
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
variable {G:Gauge}{k e u₀:ℕ}{R:Run G}{Q:J→SealR G}{own:∀s,Rails (Q s).h k u₀ e}
    {V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}
    {ι:J→Type*}{P:(s:J)→ι s→TowerS G (Q s).D}{A:(s:J)→ι s→ℝ}{u b host m K N:ℕ}
variable (T:Assigned R Q own V coins j port ι P A u b host m K N)(pick:(s:J)→Bool→ι s)


open WilsonIndependentConditionedFolioReader (ear site)
open WilsonIndependentNotebookComplexCorners (reader)
open WilsonIndependentConditionedFolioReader (price locations pair)

def bill (φ:(s:J)→Rarity (Q s).D)(y:ℝ)(o:CellR)(z:Fin 0→YForest G)(q:ℕ)(g:ℝ)(b c:Bool):ℂ:=
  let idx:=fun s:J=>pick s (if s=0 then b else c)
  let t:=paceT V.draws.S m K
  ∑n∈canvasM (φ 0) t y,∑p∈canvasM (φ 1) t y,ear q g z (cruises V.draws V.paid N (k+k) K host
    (agateV (site (P 0 (idx 0)) (φ 0) t y o (Q 0).h n) (site (P 1 (idx 1)) (φ 1) t y o (Q 1).h p)))

theorem original (older:host ≤ m)(cut:m ≤ K)(top:K ≤ N)
    (φ:(s:J)→Rarity (Q s).D)(y:ℝ)(o:CellR)(z:Fin 0→YForest G)(q:ℕ)(g:ℝ)(b c:Bool):
    reader T pick (fun _=>1) φ y o z q g b c=bill (P:=P) (host:=host) (m:=m) (K:=K) (N:=N)
      (V:=V) (k:=k) (Q:=Q) pick φ y o z q g b c:=by
  classical
  let idx:=fun s:J=>pick s (if s=0 then b else c)
  let X:=fun s=>T.cuts s (idx s)
  let t:=paceT V.draws.S m K
  have comp (s:J):input Q own C C C C X s 1 (φ s) y o=
      ∑n∈canvasM (φ s) t y,site (P s (idx s)) (φ s) t y o (Q s).h n:=by
    unfold WilsonIndependentConditionedBankCorner.input X
    rw [one_smul,T.input,T.levels,T.home,T.birth]
    exact locations .. 
  have paid (s:J):On k (P s (idx s)):=(T.input s (idx s)) ▸ (T.cuts s (idx s)).sp
  change view (X 0) host q g (input Q own C C C C X 0 1 (φ 0) y o) (input Q own C C C C X 1 1 (φ 1) y o) z=_
  rw [comp,comp]
  unfold view WilsonIndependentFittedMixedReturn.word
  change ear q g z (cruises (X 0).ax (X 0).tx (X 0).N (k+k) ((X 0).m+(X 0).i) host _) =_
  rw [show (X 0).ax=V.draws from T.levels ..,show (X 0).tx=V.paid from T.reset ..,
    show (X 0).N=N from T.vacuum ..,show (X 0).m+(X 0).i=K from T.birth ..]
  unfold bill
  exact pair V (older.trans cut) top _ _ _ _ (fun n _=>price (paid 0) _ _ _ _ _ n)
    (fun p _=>price (paid 1) _ _ _ _ _ p) q g z

end YM.Integration.WilsonIndependentConditionedFolioCuts
end
