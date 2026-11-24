import YM.Integration.WilsonIndependentConditionedBankTable

/-! One normalized bilinear response on the public Wick coordinates, shared by every preparation. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankPublicGram
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

def internal (R:Realm G (e+1) L)(Q:SealR G)(host m N:ℕ)(v:Q.Rider)(i:Alma Q.F):Cost:=
  clock R.draws R.paid N m host (PermuteLens R.draws R.paid Q N m v i)

def response (R:Realm G (e+1) L)(Q₁ Q₂:SealR G)(k host m K N:ℕ)
    (φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(y:ℝ)(o:CellR)(s:ℕ)(z:Fin s→YForest G)
    (q:ℕ)(g:ℝ)(u:Q₁.Rider)(v:Q₂.Rider):ℂ:=
  ∑i,∑j,(measured q g (internal R Q₁ host m N u i)*measured q g (internal R Q₂ host m N v j))*
    measured q g (measure R Q₁ Q₂ k m K N host φ ψ y o s z i j)

def residual (R:Realm G (e+1) L)(Q₁ Q₂:SealR G)(k host m K N:ℕ)
    (φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(y:ℝ)(o:CellR)(s:ℕ)(z:Fin s→YForest G)
    (q:ℕ)(u:Q₁.Rider)(v:Q₂.Rider):ℝ:=
  ∑i,∑j,(belt q (embed (internal R Q₁ host m N u i))*belt q (embed (internal R Q₂ host m N v j)))*
    belt q (embed (measure R Q₁ Q₂ k m K N host φ ψ y o s z i j))

theorem pivots (X:CutsP H Q₁.ans Q₁.path v₁ E W K U)(R:Realm G (e+1) L)
    (host m N:ℕ)(files:X.ax=R.draws)(reset:X.tx=R.paid)(home:X.m=m)(top:X.N=N)(a:ℝ):
    weights X host (dose X a)=internal R Q₁ host m N (publicDose Q₁ X a):=by
  unfold internal weights
  rw [←files,←reset,←top,←home,(WilsonPositionProgramTrialHomeDose.original Q₁ X a).1]

theorem original (R:Realm G (e+1) L)
    (X:CutsP H Q₁.ans Q₁.path v₁ E W K U)(Y:CutsP H Q₂.ans Q₂.path v₂ E W K U)
    (m K' N host:ℕ)(older:host ≤ m)
    (filesX:X.ax=R.draws)(resetX:X.tx=R.paid)(homeX:X.m=m)(startX:X.ceilC=K')(topX:X.N=N)
    (filesY:Y.ax=R.draws)(resetY:Y.tx=R.paid)(homeY:Y.m=m)(startY:Y.ceilC=K')(topY:Y.N=N)
    (a b:ℝ)(φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(y:ℝ)(o:CellR)(s:ℕ)(z:Fin s→YForest G)
    (q:ℕ)(g:ℝ)(small:|g|≤1):
    let x:=publicDose Q₁ X a; let y':=publicDose Q₂ Y b
    let issued:=raw X host (receiving X a φ y o X.i) (receiving Y b ψ y o Y.i) s z
    ‖measured q g issued-response R Q₁ Q₂ k host m K' N φ ψ y o s z q g x y'‖ ≤
      3*|g|^(q+1)*residual R Q₁ Q₂ k host m K' N φ ψ y o s z q x y':=by
  intro x y' issued
  have bill:=WilsonIndependentConditionedBankGram.numerical X Y (filesY.trans filesX.symm)
    (resetY.trans resetX.symm) (topY.trans topX.symm) (homeY.trans homeX.symm)
    (startY.trans startX.symm) host (homeX ▸ older) (dose X a) (dose Y b) φ ψ y o s z q g small
  dsimp only at bill
  rw [WilsonIndependentConditionedBankTable.original R X Y m K' N host filesX resetX homeX startX topX
    filesY resetY homeY startY topY φ ψ y o s z,pivots X R host m N filesX resetX homeX topX a,
    pivots Y R host m N filesY resetY homeY topY b] at bill
  exact bill

end YM.Integration.WilsonIndependentConditionedBankPublicGram
