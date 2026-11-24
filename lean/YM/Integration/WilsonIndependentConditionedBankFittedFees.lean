import YM.Integration.WilsonIndependentConditionedBankFour
import YM.Integration.WilsonIndependentFittedHomeReserve
import YM.Integration.WilsonIndependentMovingRosterDoseCost

/-! The genuine old clocks and original graded costs for every preparation, uniform in its higher cutoff. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankFittedFees
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
variable {G:Gauge}{h D e k u u₀:ℕ}
local notation "J" => Fin 2
local notation "C" => Credit.leanC

open WilsonIndependentConditionedBankCorner (Bill input)
open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedPairProbes (Prices charge)
open WilsonIndependentConditionedPairTrialCost (roof)
open WilsonIndependentFittedPivotCash (view)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentConditionedBankPublicGram (response)
open WilsonPositionProgramTrialHomeDose (publicDose)

open WilsonIndependentConditionedBankCash (reserve)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentFittedStoppedWage (window)
open WilsonOriginalPublicPlantedStableCredit (span)

def age (R:Run G)(m K:ℕ):ℝ:=
  zz R.family.path.levels m+(R.family.path.levels.S.scale K-R.family.path.levels.S.scale m)+(K-m:ℕ)

variable {R:Run G}{Q:J→SealR G}{own:∀s,Rails (Q s).h k u₀ e}
    {V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}
    {ι:J→Type*}{P:(s:J)→ι s→TowerS G (Q s).D}{A:(s:J)→ι s→ℝ}{b host m K N:ℕ}

theorem accounts (T:Assigned R Q own V coins j port ι P A u b host m K N)(s:J)(i:ι s):
    let X:=T.cuts s i
    X.vesselsC.anchor=j ∧ X.vesselsC.y=zz R.family.path.levels ∧ X.ax=R.family.path.levels:=by
  intro X
  change X.L.L.V.anchor=j ∧ X.L.L.V.y=zz R.family.path.levels ∧ X.L.L.V.draws=R.family.path.levels
  dsimp only [X]
  rw [T.lantern]
  exact ⟨(port s).anchor,(port s).age,(port s).levels⟩

theorem acquired (T:Assigned R Q own V coins j port ι P A u b host m K N)(s:J)(i:ι s)
    (openDate:j ≤ host)(older:host ≤ m):
    let X:=T.cuts s i
    ∃live:X.vesselsC.anchor ≤ host,∃date:host ≤ X.m,
      (window X host live date).Age=age R host m ∧ X.Age=age R m K ∧
        (Real.exp (span X X.i))^(Q s).h=(paceT R.family.path.levels.S m K^(Q s).h)⁻¹:=by
  intro X
  obtain ⟨first,prices,levels⟩:=accounts T s i
  have hX:X.m=m:=T.home s i
  have kX:X.m+X.i=K:=T.birth s i
  have diff:X.i=K-m:=by omega
  have hX':host+(m-host)=m:=by omega
  refine ⟨first ▸ openDate,hX ▸ older,?_,?_,?_⟩
  · change X.vesselsC.y host+(X.ax.S.scale (host+(X.m-host))-X.ax.S.scale host)+(X.m-host:ℕ)=_
    rw [hX,hX',prices,levels];rfl
  · change X.vesselsC.y X.m+(X.ax.S.scale (X.m+X.i)-X.ax.S.scale X.m)+(X.i:ℝ)=_
    rw [kX,hX,diff,prices,levels];rfl
  · rw [WilsonIndependentMovingRosterDoseCost.rate,levels,hX,T.birth]

theorem original (Q:J→SealR G)(own:∀s,Rails (Q s).h k u₀ e):∃C₁ C₂:J→Credit,
    ∀{R:Run G}{V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}
    {ι:J→Type*}{P:(s:J)→ι s→TowerS G (Q s).D}{A:(s:J)→ι s→ℝ}{b host m K N:ℕ}
    (T:Assigned R Q own V coins j port ι P A u b host m K N),j ≤ host → host ≤ m →
    ∀(s:J)(i:ι s)(a:ℝ)(q:ℕ),q ≤ e →
    let X:=T.cuts s i
    reserve X host q (dose X a)≤
      (Fintype.card (Alma (Q s).F):ℝ)*((q+1:ℕ):ℝ)*((C₁ s).buy (age R host m)*
        ((paceT R.family.path.levels.S m K^(Q s).h)⁻¹*(C₂ s).buy (age R m K)*(|a| *A s i))):=by
  choose C₁ C₂ offer using fun s=>WilsonIndependentFittedStoppedWage.original (hol G)
    (Q s).ans (Q s).path (own s) C C C C
  refine ⟨C₁,C₂,?_⟩
  intro R V coins j port ι P A b host m K N T opened older s i a q cap X
  obtain ⟨live,date,oldAge,newAge,pole⟩:=acquired T s i opened older
  have cash:=offer s X host a 1 live date q cap
  have result:=WilsonIndependentFittedHomeReserve.reserve X host q (dose X a) _ cash
  rw [oldAge,newAge,pole,T.price] at result
  exact result

end YM.Integration.WilsonIndependentConditionedBankFittedFees
