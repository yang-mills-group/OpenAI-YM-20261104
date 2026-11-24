import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedWage
import YM.Integration.WilsonOriginalPublicTrialPhaseFourDictionary

/-! The physical angular input norm in its original field basis. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedFrame
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

open WilsonPositionProgramTrialPublicJointFourSignedWage (fieldSize)
open WilsonOriginalPublicTrialPhaseFourDictionary (Kept seat seat_sheet rank_zero)

theorem original (F:Frame G 4)(simple:G.Simple)(v:F.Coeff)(p:ℂ →L[ℝ] ℝ):
    fieldSize v p=∑j:F.Index,|p (strip v j)|:=by
  classical
  let held (a:Alma F)(ha:rankS (notar F a)=0):Kept F:=
    ⟨a,fun h=>by have lt:=h.2;omega⟩
  let flat:=Finset.univ.filter fun a:Alma F=>rankS (notar F a)=0
  calc
    fieldSize v p=∑a∈flat,|p (strip v (sheet F a))|:=by
      rw [fieldSize,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      change |if rankS (notar F a)=0 then p (strip v (sheet F a)) else 0|=_
      split_ifs <;> simp
    _=∑j:F.Index,|p (strip v j)|:=by
      refine Finset.sum_bij (fun a _=>sheet F a) (fun _ _=>Finset.mem_univ _) ?_ ?_ (by intros;rfl)
      · intro a ha b hb same
        have af:rankS (notar F a)=0:=(Finset.mem_filter.mp ha).2
        have bf:rankS (notar F b)=0:=(Finset.mem_filter.mp hb).2
        have first: (seat F (sheet F a)).val=a:=congrArg Subtype.val (seat_sheet F simple (held a af))
        have last: (seat F (sheet F b)).val=b:=congrArg Subtype.val (seat_sheet F simple (held b bf))
        exact first.symm.trans ((congrArg (fun j=>(seat F j).val) same).trans last)
      · intro j _
        exact ⟨(seat F j).val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rank_zero F simple _⟩,rfl⟩

end YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedFrame
