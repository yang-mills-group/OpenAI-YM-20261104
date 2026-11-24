import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedSource
import YM.Integration.WilsonIndependentMatchedPhysicalPeer

/-! The uncompounded public field norm pays both quadratic-input wages. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedWage
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
open WilsonPositionProgramTrialPublicJointFourSignedSource (strip amountStrip rank)
open WilsonIndependentMatchedFiledIncome (allot)

def fieldSize {F:Frame G 4}(v:F.Coeff)(p:ℂ →L[ℝ] ℝ):ℝ:=∑a,|amount (strip v) p a|
def wage {F:Frame G 4}(e:ℕ)(A:Alma F→ℝ)(b:Blue.Cost):ℝ:=∑a,allot e b (A a)

theorem rescale (e:ℕ)(b:Blue.Cost)(x A:ℝ):
    allot e (C x*b) A=|x| * allot e b A:=by
  simp only [allot,coeff_C_mul,abs_mul,Finset.mul_sum,mul_assoc]

theorem linear {F:Frame G 4}(e:ℕ)(A:Alma F→ℝ)(positive:∀i,0 ≤ A i)
    (v:F.Coeff)(p:ℂ →L[ℝ] ℝ)(b:Blue.Cost):
    WilsonIndependentMatchedFiledIncome.charge e (fun a=>C (amount (strip v) p a)*b) A ≤ wage e A b*fieldSize v p:=by
  unfold WilsonIndependentMatchedFiledIncome.charge wage
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  rw [rescale,mul_comm]
  apply mul_le_mul_of_nonneg_left _ (WilsonIndependentMatchedFiledIncome.nonneg (positive a) b e)
  exact Finset.single_le_sum (fun i _=>abs_nonneg (amount (strip v) p i)) (Finset.mem_univ a)

theorem original {F:Frame G 4}(simple:G.Simple)(e:ℕ)(A:Alma F→ℝ)(positive:∀i,0 ≤ A i)
    (v:F.Coeff)(p:ℂ →L[ℝ] ℝ):
    WilsonIndependentMatchedFiledIncome.charge e (picked v p 2) A ≤ wage e A 1*fieldSize v p ∧
    WilsonIndependentMatchedFiledIncome.charge e (written F (strip v) p) A ≤ wage e A (PowerSeries.X^2)*fieldSize v p:=by
  have ground:picked v p 2=(fun a=>C (amount (strip v) p a)*1):=by
    funext a
    by_cases unit:sheet F a=0
    · have z:valence F a=0:=by rw [valence,unit,F.zero_degree]
      simp [picked,z,amountStrip,unit]
    · simp [picked,rank simple a unit,amountStrip,unit]
  have suspended:written F (strip v) p=(fun a=>C (amount (strip v) p a)*PowerSeries.X^2):=by
    funext a
    rw [WilsonPositionProgramTrialPublicJointGroundPortfolio.intrinsic]
    by_cases unit:sheet F a=0
    · simp [amountStrip,unit]
    · rw [rank simple a unit]
  rw [ground,suspended]
  exact ⟨linear e A positive v p 1,linear e A positive v p (PowerSeries.X^2)⟩

end YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedWage
