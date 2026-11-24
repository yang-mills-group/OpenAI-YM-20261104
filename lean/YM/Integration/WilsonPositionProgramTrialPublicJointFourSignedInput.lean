import YM.Integration.WilsonPositionProgramTrialPublicJointFourVotedSheet
import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedFrame

/-! Reindex the signed optical input on the actual fitted angular field. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedInput
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

open WilsonPositionProgramTrialPublicJointGroundVoted (bid)
open WilsonMovingForkMixedSeed (doses)
open Trace.Physical.GermGraph

open WilsonPositionProgramTrialPublicJointFourSignedSource (strip)
open WilsonPositionProgramTrialPublicJointFourSignedWage (fieldSize)

variable {n K:ℕ}(N per:ℕ)(file:Filed R (fun _:Fin n=>4) K)(Y:Fin n→R.family.label 4)(turn:Fin n→Motion)
local notation "Z" => R.family.labels.level 4

def turned (i:Fin n):(Z).Coeff:=Motion.patch Z (turn i)
  ((file.A N per i).symm (fitted R 4 (file.station i) N per (Y i)))

def income (r s:ℝ):ℝ:=(r^4)⁻¹*s*(regulatorRun R.family N per K/(R.family.path.rep N per K).p.threshold)^2

theorem seat (simple:G.Simple)(r:ℝ)(rp:0<r)(s:ℝ)(i:Fin n)(p:ℂ →L[ℝ] ℝ)
    (j:(Z).Index)(nonunit:j≠0):
    p (bid R (fun _:Fin n=>4) N per file Y turn r (s:ℂ) i j)=
      income (K:=K) R N per r s * p (turned R N per file Y turn i j):=by
  rw [WilsonPositionProgramTrialPublicJointFourVotedSheet.original R (fun _:Fin n=>4) N per file Y turn r rp (s:ℂ) i j,
    WilsonOriginalPublicTrialPhaseFourDictionary.weight Z simple j nonunit]
  change p (_* (turned R N per file Y turn i j))=_
  have real:((r:ℂ)^4)⁻¹*(s:ℂ)*((regulatorRun R.family N per K/(R.family.path.rep N per K).p.threshold)^2:ℝ)=
      ((income (K:=K) R N per r s:ℝ):ℂ):=by simp [income]
  rw [real,←Complex.real_smul,p.map_smul]
  rfl

theorem active (simple:G.Simple)(r:ℝ)(rp:0<r)(s:ℝ)(i:Fin n)(p:ℂ →L[ℝ] ℝ)
    (a:Alma Z)(positive:sheet Z a≠0):
    amount (bid R (fun _:Fin n=>4) N per file Y turn r (s:ℂ) i) p a=
      income (K:=K) R N per r s * p (turned R N per file Y turn i (sheet Z a)):=by
  have h:rankS a.val.2=0:=(WilsonPositionProgramTrialPublicJointFourLive.grades Z simple le_rfl a positive).2
  simpa only [amount,if_pos h] using seat R N per file Y turn simple r rp s i p _ positive

theorem size (simple:G.Simple)(r:ℝ)(rp:0<r)(s:ℝ)(i:Fin n)(p:ℂ →L[ℝ] ℝ):
    fieldSize (bid R (fun _:Fin n=>4) N per file Y turn r (s:ℂ) i) p=
      |income (K:=K) R N per r s| * fieldSize (turned R N per file Y turn i) p:=by
  rw [WilsonPositionProgramTrialPublicJointFourSignedFrame.original Z simple,
    WilsonPositionProgramTrialPublicJointFourSignedFrame.original Z simple,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h:j=0
  · simp [strip,h]
  · simp only [strip,if_neg h,seat R N per file Y turn simple r rp s i p j h,abs_mul]

end YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedInput
