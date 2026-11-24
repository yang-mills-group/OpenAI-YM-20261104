import YM.Integration.WilsonIndependentConditionedBankFittedFees

/-! The first-join tariff has one explicit spacing power, with both old clocks and original salaries on the selected degrees. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankShellPrice
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

open WilsonIndependentMatchedRosterMasks (Bits choose)
open WilsonIndependentMatchedRosterSlots (degree)
open WilsonIndependentMatchedProxyIncome (tariff)
open WilsonIndependentConditionedBankFittedFees (age accounts acquired)
open WilsonIndependentConditionedBankAxes (allowance)

def wage (R:Run G)(Q:J→SealR G)(coins:Prices)(u b host m K:ℕ)
    (ζ:ℝ)(a A B:J→ℝ)(t z:ℝ)(mask:Bits 1):ℝ:=
  let d:=choose 1 mask
  let degrees:=fun i=>degree (d i) k (Q i).h
  let bills:=fun i=>if d i then (coins.slot mask i).buy (age R m K)*(|a i| * A i)
    else (tariff (hol G) (Q i).ans (Q i).path e u b C C C).buy (age R m K)
  (coins.stop mask).buy (age R host m)*WilsonIndependentConditionedLocalRate.fee (2*k) e u b degrees t z bills B
    ((coins.window mask).buy (age R m K)) ((∑i,(Q i).h:ℕ):ℝ) ζ

theorem original {R:Run G}{Q:J→SealR G}{own:∀s,Rails (Q s).h k u₀ e}
    {V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}
    {ι:J→Type*}{P:(s:J)→ι s→TowerS G (Q s).D}{A:(s:J)→ι s→ℝ}{u b host m K N:ℕ}
    (T:Assigned R Q own V coins j port ι P A u b host m K N)(openDate:j ≤ host)(older:host ≤ m)
    (ageV:V.y=zz R.family.path.levels)(pick:(s:J)→ι s)
    (ζ:ℝ)(a B:J→ℝ)(t z:ℝ):
    let X:=fun s=>T.cuts s (pick s)
    let F:=charge Q own C C C C V X coins u b host m K ζ a B t z
    let B₀:=wage (k:=k) (e:=e) R Q coins u b host m K ζ a (fun i=>A i (pick i)) B t z
    let δ:=paceT R.family.path.levels.S m K
    (∀mask,F mask=B₀ mask*δ^ζ) ∧ roof F=roof B₀*δ^ζ:=by
  intro X F B₀ δ
  have levels:V.draws=R.family.path.levels:=
    (T.levels 0 (pick 0)).symm.trans (accounts T 0 (pick 0)).2.2
  have ageX (s:J):(X s).Age=age R m K:=
    (acquired T s (pick s) openDate older).choose_spec.choose_spec.2.1
  have count (t s:ℕ):WilsonIndependentMatchedCoverDate.age V t s=age R t s:=by
    unfold WilsonIndependentMatchedCoverDate.age WilsonIndependentConditionedBankFittedFees.age
    rw [ageV,levels]
  have tickets (mask:Bits 1)(D:J→ℝ):
      WilsonIndependentConditionedBankAxes.allowance Q own C C C C X (choose 1 mask) D u b=
        fun s=>if choose 1 mask s then D s else
          (tariff (hol G) (Q s).ans (Q s).path e u b C C C).buy (age R m K):=by
    funext s
    simp only [WilsonIndependentConditionedBankAxes.allowance,ageX]
  have eqn (mask:Bits 1):F mask=B₀ mask*δ^ζ:=by
    simp only [F,B₀,WilsonIndependentConditionedPairProbes.charge,wage,tickets,ageX,count,δ,levels,X,T.price,mul_assoc]
  refine ⟨eqn,?_⟩
  have good:0≤δ^ζ:=Real.rpow_nonneg (div_nonneg (R.family.path.levels.S.a_pos K).le (R.family.path.levels.S.a_pos m).le) _
  simp only [WilsonIndependentConditionedPairTrialCost.roof,eqn,max_mul_of_nonneg _ _ good,zero_mul]

end YM.Integration.WilsonIndependentConditionedBankShellPrice
