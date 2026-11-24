import YM.Integration.WilsonIndependentNotebookComplexQuadrant
import YM.Integration.WilsonIndependentConditionedBankFour

/-! Relative errors of four real measurements on the identical assigned Wilson arrays. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookComplexCorners
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

def assembled (a:J→ℝ)(q:ℕ)(g:ℝ)(s:J)(c:Bool):Alma (Q s).F→ℂ:=
  sample V (Q s) N m host q g (publicDose (Q s) (T.cuts s (pick s c)) (a s))

def reader (a:J→ℝ)(φ:(s:J)→Rarity (Q s).D)(y:ℝ)(o:CellR)(z:Fin 0→YForest G)(q:ℕ)(g:ℝ)(c d:Bool):ℂ:=
  let X:=fun s:J=>T.cuts s (pick s (if s=0 then c else d))
  let O:=fun s=>input Q own C C C C X s (a s) (φ s) y o
  view (X 0) host q g (O 0) (O 1) z

theorem original (older:host ≤ m)(a:J→ℝ)(φ:(s:J)→Rarity (Q s).D)(y:ℝ)(o:CellR)
    (z:Fin 0→YForest G)(q:ℕ)(g:ℝ)(θ:J→Motion){ε:ℝ}(non:0≤ε):
    let x:=assembled T pick a q g
    let Y:=reader T pick a φ y o z q g
    let d:=fun (s:J)(i:Alma (Q s).F)=>fuse (θ s) (fun c=>x s c i)
    (∀c t,‖Y c t-response V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 z q g
      (publicDose (Q 0) (T.cuts 0 (pick 0 c)) (a 0)) (publicDose (Q 1) (T.cuts 1 (pick 1 t)) (a 1))‖≤
      ε*(1+∑i,‖x 0 c i‖)*(1+∑i,‖x 1 t i‖)) →
    ‖fuse (θ 0) (fun c=>fuse (θ 1) (Y c))-
      protocol V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 z q g (d 0) (d 1)‖≤
      4*ε*(1+∑i,‖d 0 i‖)*(1+∑i,‖d 1 i‖):=by
  intro x Y d signed
  have row (s:J)(c:Bool):(1+∑i,‖x s c i‖)≤1+∑i,‖d s i‖:=by
    apply add_le_add le_rfl
    refine Finset.sum_le_sum fun i _=>axes (θ s) (fun h=>x s h i) (fun h=>?_) c
    exact WilsonIndependentNotebookComplexQuadrant.real_fee q g _
  let Gr:=protocol V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 z q g
  have each (c t:Bool):‖Y c t-Gr (x 0 c) (x 1 t)‖≤ε*(1+∑i,‖d 0 i‖)*(1+∑i,‖d 1 i‖):=by
    have pay:=signed c t
    rw [WilsonIndependentConditionedBankMatrix.original V _ _ m K N host older
      (T.levels 0 (pick 0 c)) (T.reset 0 (pick 0 c)) (T.home 0 (pick 0 c)) (T.vacuum 0 (pick 0 c))
      (T.levels 1 (pick 1 t)) (T.reset 1 (pick 1 t)) (T.home 1 (pick 1 t)) (T.vacuum 1 (pick 1 t))
      (a 0) (a 1) (φ 0) (φ 1) y o 0 z q g] at pay
    exact pay.trans (mul_le_mul (mul_le_mul_of_nonneg_left (row 0 c) non) (row 1 t) (by positivity) (by positivity))
  rw [show protocol V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 z q g (d 0) (d 1)=
    fuse (θ 0) (fun c=>fuse (θ 1) (fun t=>Gr (x 0 c) (x 1 t))) from
      WilsonIndependentNotebookComplexQuadrant.measured V _ _ k host m K N (φ 0) (φ 1) y o 0 z q g (θ 0) (θ 1) (x 0) (x 1)]
  exact (WilsonIndependentNotebookComplexQuadrant.quartet _ _ _ _ each).trans_eq (by ring)
end YM.Integration.WilsonIndependentNotebookComplexCorners
