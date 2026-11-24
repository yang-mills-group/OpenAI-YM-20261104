import YM.Integration.WilsonIndependentConditionedBankPublicGram
import YM.Integration.WilsonIndependentNotebookDoseCoefficients

/-! Both genuine source doses are evaluated before insertion in the same independent Gram matrix. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankMatrix
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonIndependentFittedMixedReturn (word planted)
open WilsonIndependentFittedMixedCash (bill embed)
open WilsonIndependentMatchedPivotStop (Hearing)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedFittedSeat (dose receiving)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentFittedPivotCash (measured view gross)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonIndependentConditionedBankCash (amount reserve)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
variable {G:Gauge}{k e u₀:ℕ}{H:Hol G}{Q₁ Q₂:SealR G}
    {v₁:Rails Q₁.h k u₀ e}{v₂:Rails Q₂.h k u₀ e}{E W K U:Credit}

open WilsonIndependentConditionedBankPair (Cut)
open WilsonIndependentFittedMixedReturn (planted)
open WilsonIndependentMatchedPivotSeat (axis)
local notation "raw" => WilsonIndependentFittedMixedReturn.word


variable {L:Credit}

open WilsonIndependentConditionedBankTable (measure)
open WilsonIndependentConditionedBankGram (weights)
open WilsonPositionProgramTrialHomeDose (publicDose)

open WilsonIndependentConditionedBankPublicGram (internal response pivots)

def sample (R:Realm G (e+1) L)(Q:SealR G)(N m host q:ℕ)(g:ℝ)(d:Q.Rider)(j:Alma Q.F):ℂ:=
  measured q g (clock R.draws R.paid N m host (d j))

def pivot (R:Realm G (e+1) L)(Q:SealR G)(N m:ℕ)(x:Alma Q.F→ℂ)(i:Alma Q.F):ℂ:=
  ∑j,((Wray R.draws R.paid Q.ans Q.path N m)⁻¹ i j) • x j

def protocol (R:Realm G (e+1) L)(Q₁ Q₂:SealR G)(k host m K N:ℕ)
    (φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(y:ℝ)(o:CellR)(s:ℕ)(z:Fin s→YForest G)
    (q:ℕ)(g:ℝ)(x:Alma Q₁.F→ℂ)(v:Alma Q₂.F→ℂ):ℂ:=
  ∑i,∑j,(pivot R Q₁ N m x i*pivot R Q₂ N m v j)*measured q g (measure R Q₁ Q₂ k m K N host φ ψ y o s z i j)

theorem chart (R:Realm G (e+1) L)(Q:SealR G)(v:Rails Q.h k u₀ e)
    (X:CutsP H Q.ans Q.path v E W K U)(m N host:ℕ)(older:host ≤ m)
    (files:X.ax=R.draws)(reset:X.tx=R.paid)(home:X.m=m)(top:X.N=N)(q:ℕ)(g a:ℝ)(i:Alma Q.F):
    measured q g (internal R Q host m N (publicDose Q X a) i)=
      pivot R Q N m (sample R Q N m host q g (publicDose Q X a)) i:=by
  rw [←congrFun (pivots X R host m N files reset home top a) i]
  have h:=WilsonIndependentNotebookDoseCoefficients.coefficients H Q v E W K U X a host q (home ▸ older) g
  change cash q g (embed (clock X.ax X.tx X.N X.m host (dose X a i)))=
    ∑j,((Wray R.draws R.paid Q.ans Q.path N m)⁻¹ i j) •
      cash q g (embed (clock R.draws R.paid N m host (publicDose Q X a j)))
  simpa only [←files,←reset,←home,←top] using h.1 i

theorem original (R:Realm G (e+1) L)
    (X:CutsP H Q₁.ans Q₁.path v₁ E W K U)(Y:CutsP H Q₂.ans Q₂.path v₂ E W K U)
    (m K' N host:ℕ)(older:host ≤ m)
    (filesX:X.ax=R.draws)(resetX:X.tx=R.paid)(homeX:X.m=m)(topX:X.N=N)
    (filesY:Y.ax=R.draws)(resetY:Y.tx=R.paid)(homeY:Y.m=m)(topY:Y.N=N)
    (a b:ℝ)(φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(y:ℝ)(o:CellR)(s:ℕ)(z:Fin s→YForest G)(q:ℕ)(g:ℝ):
    let x:=publicDose Q₁ X a; let t:=publicDose Q₂ Y b
    response R Q₁ Q₂ k host m K' N φ ψ y o s z q g x t=
      protocol R Q₁ Q₂ k host m K' N φ ψ y o s z q g
        (sample R Q₁ N m host q g x) (sample R Q₂ N m host q g t):=by
  intro x t
  unfold response protocol
  simp only [x,t,chart R Q₁ v₁ X m N host older filesX resetX homeX topX,
    chart R Q₂ v₂ Y m N host older filesY resetY homeY topY]

end YM.Integration.WilsonIndependentConditionedBankMatrix
