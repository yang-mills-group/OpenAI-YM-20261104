import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedFitted
import YM.Integration.WilsonOriginalPublicTrialPhaseMotion
import YM.Integration.WilsonMeasuredSignedActionMeasuredLimit

/-! A genuine unturned physical field on its own deposited K word. All
21 measured directions use the same filed vote, with its unit left free. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonMeasuredSignedActionDeposited
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace
open WilsonSurveyedEquationFrameInlet (bank master loan price)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (W : Initialize G) {h hi D k u e : ℕ}
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC


open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonPositionProgramTrialPublicJointCapFiling (sectionAt)
open WilsonSurveyedEquationFrameStability (course)

open WilsonPositionProgramTrialPublicJointCapArrival (high own linear)


open PowerSeries Matrix WilsonCoeffUV.Bank.Carp

open WilsonPositionProgramTrialStationHome (age)
open WilsonPositionProgramTrialAccrued (home)
open WilsonPositionProgramTrialPublicJointGroundBirth (accrued)

open WilsonOriginalPhysicalFruitVerse (written)
open WilsonPositionProgramTrialPublicJointGroundPortfolio (amount)
open WilsonOriginalPublicNodalDeployedVote (vector)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonPositionProgramReportedField (entire)
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open PhysicalNext.Repeat.Legato Extra.Histories Pert.Asymptotics

open WilsonPositionProgramTrialPublicJointGroundHead (picked)
open WilsonIndependentMatchedPhysicalPeer (reading)

open WilsonPositionProgramTrialPublicJointFourSignedSource (strip)
open WilsonPositionProgramTrialPublicJointFourSignedWage (fieldSize wage)

open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonPositionProgramTrialPublicJointGroundVoted (bid)
open WilsonPositionProgramTrialPublicJointFourSignedInput (turned income)
open WilsonOriginalPublicTrialPhaseFourDictionary (seat Kept)
local notation "F₀" => R.family.labels.level 4

open WilsonPositionProgramTrialPublicJointFourSignedFitted (field coefficient)
def filled (F:Frame G 4)(b:F.Coeff)(unit:ℂ):F.Coeff:=
  fun i=>if i=0 then unit else b i

theorem cleared (F:Frame G 4)(b:F.Coeff)(unit:ℂ)(zero:b 0=0):F.core (filled F b unit)=b:=by
  funext j
  by_cases cut:j=0
  · subst j
    simp [Frame.core,zero]
  · simp [filled,Frame.core,cut]

private theorem swap (F:Frame G 4)(x y:F.Coeff):F.coeffSize (x-y)=F.coeffSize (y-x):=by
  exact Finset.sum_congr rfl (fun _ _=>norm_sub_rev ..)

theorem original (simple:G.Simple)(v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    (fit:4<D)(rails:Rails 4 k u e)(enough:4 ≤ k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>4) (fun _=>D) (fun _=>fit)) ≤ k)
    (T:SectionData F₀){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (width η:ℝ)(wide:0≤width)(gain:0<η)(margin:2*η ≤ 1):
    ∃M:ℝ,0 ≤ M ∧ ∀ᶠ j:ℕ in atTop,∀ m K N per:ℕ,j ≤ m → m ≤ K → K ≤ N →
    let t:=regulatorRun R.family N per m
    let g:=regulatorRun R.family N per K
    0<t → t≤1 → g≠0 → (L).S.a m/(L).S.a K ≤ t^(-width) → (L).S.a K/(L).S.a m ≤ t^(8*η) →
    ∀q:ℕ,2 ≤ q → q ≤ e → ∀{n:ℕ}(file:Filed R (fun _:Fin n=>4) K)
      (Y:Fin n→R.family.label 4)(r:ℝ),0<r → ∀(i:Fin n)(unit:ℂ),
      let b:=filled F₀ (field R fit k T m N per file Y (fun _=>(1,false)) r 1 i q) unit
      let w:=(file.A N per i).symm (fitted R 4 (file.station i) N per (Y i))
      let x:=(coefficient R m K N per r 1:ℂ) • (F₀).core w
      (F₀).coeffSize (x-(F₀).core b) ≤ M*t^η*(F₀).coeffSize x:=by
  obtain ⟨M,M₀,original⟩:=WilsonPositionProgramTrialPublicJointFourSignedFitted.original R simple
    v₀ funded fit rails enough capacity T sound pop width η wide gain margin
  refine ⟨M,M₀,?_⟩
  filter_upwards [original] with j bought
  intro m K N per late below top t g t₀ hot good minBound maxBound q floor degree n file Y r rp i unit b w x
  have held:=bought m K N per late below top t₀ hot good minBound maxBound q floor degree file Y
    (fun _=>(1,false)) r 1 rp zero_le_one i
  let zeroField:=field R fit k T m N per file Y (fun _=>(1,false)) r 1 i q
  have z:zeroField 0=0:=by
    simp [zeroField,field,WilsonPositionProgramTrialPublicJointFourSignedComplex.field,Frame.core]
  rw [show (F₀).core b=zeroField from cleared F₀ zeroField unit z,swap]
  simpa only [zeroField,x,w,WilsonPositionProgramTrialPublicJointFourSignedInput.turned,WilsonOriginalPublicTrialPhaseMotion.plain] using held

end YM.Integration.WilsonMeasuredSignedActionDeposited
