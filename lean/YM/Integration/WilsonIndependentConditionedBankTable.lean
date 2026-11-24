import YM.Integration.WilsonIndependentConditionedBankGram
import YM.Integration.WilsonIndependentConditionedBankRelative

/-! The pivot Gram only uses the physical chart, common N quiet and the two chosen profiles. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankTable
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
def direction (R:Realm G (e+1) L)(Q:SealR G)(m K N:ℕ)(φ:Rarity Q.D)(y:ℝ)(o:CellR)(i:Alma Q.F):Era G ℝ:=
  locale o (Q.spins R.draws R.paid φ m K N y (axis i 0))

def measure (R:Realm G (e+1) L)(Q₁ Q₂:SealR G)(k m K N host:ℕ)
    (φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(y:ℝ)(o:CellR)(s:ℕ)(z:Fin s→YForest G)
    (i:Alma Q₁.F)(j:Alma Q₂.F):Cost:=
  WilsonOlderFreshSoftSocketKinetic.reading (cruises R.draws R.paid N (k+k) K host
    (agateV (direction R Q₁ m K N φ y o i) (direction R Q₂ m K N ψ y o j))).2 z

theorem column (R:Realm G (e+1) L)(X:CutsP H Q₁.ans Q₁.path v₁ E W K U)
    (m K' N:ℕ)(files:X.ax=R.draws)(reset:X.tx=R.paid)(home:X.m=m)(start:X.ceilC=K')(top:X.N=N)
    (φ:Rarity Q₁.D)(y:ℝ)(o:CellR)(j:Alma Q₁.F):
    film X j 0 φ y o X.i=direction R Q₁ m K' N φ y o j:=by
  change locale o (Q₁.spins X.ax X.tx φ X.m X.ceilC X.N y (axis j 0))=_
  rw [files,reset,home,start,top]
  rfl

theorem original (R:Realm G (e+1) L)
    (X:CutsP H Q₁.ans Q₁.path v₁ E W K U)(Y:CutsP H Q₂.ans Q₂.path v₂ E W K U)
    (m K' N host:ℕ)(filesX:X.ax=R.draws)(resetX:X.tx=R.paid)(homeX:X.m=m)(startX:X.ceilC=K')(topX:X.N=N)
    (filesY:Y.ax=R.draws)(resetY:Y.tx=R.paid)(homeY:Y.m=m)(startY:Y.ceilC=K')(topY:Y.N=N)
    (φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(y:ℝ)(o:CellR)(s:ℕ)(z:Fin s→YForest G):
    WilsonIndependentConditionedBankGram.board X Y host φ ψ y o s z=measure R Q₁ Q₂ k m K' N host φ ψ y o s z:=by
  funext i j
  unfold WilsonIndependentConditionedBankGram.board WilsonIndependentFittedMixedReturn.word measure
  rw [column R X m K' N filesX resetX homeX startX topX φ y o i,
    column R Y m K' N filesY resetY homeY startY topY ψ y o j]
  change WilsonOlderFreshSoftSocketKinetic.reading (cruises X.ax X.tx X.N _ X.ceilC host _).2 z=_
  rw [filesX,resetX,startX,topX]

end YM.Integration.WilsonIndependentConditionedBankTable
