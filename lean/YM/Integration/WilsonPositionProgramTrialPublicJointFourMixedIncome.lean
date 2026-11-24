import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedInput

/-! The actual grade-four deposit inside a mixed finite physical filing. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourMixedIncome
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

local notation "Z" => R.family.labels.level 4
open WilsonPositionProgramTrialPublicJointFourSignedInput (income)

def castField {h:ℕ}(same:h=4)(v:(R.family.labels.level h).Coeff):(Z).Coeff:=same ▸ v

private theorem sheetIncome (simple:G.Simple){h K N per:ℕ}(same:h=4)(v w:(R.family.labels.level h).Coeff)
    (r s:ℝ)(paid:∀b,v b=((r:ℂ)^h)⁻¹*(s:ℂ)*
      ((regulatorRun R.family N per K/(R.family.path.rep N per K).p.threshold)^((R.family.labels.level h).grades b).2:ℝ)*w b):
    ∀j:(Z).Index,j≠0 → castField R same v j=(income (K:=K) R N per r s:ℂ)*castField R same w j:=by
  subst h
  intro j active
  change v j=_*w j
  rw [paid j,WilsonOriginalPublicTrialPhaseFourDictionary.weight Z simple j active]
  simp [WilsonPositionProgramTrialPublicJointFourSignedInput.income]

variable {n K:ℕ}(d:Fin n→ℕ)(N per:ℕ)(file:Filed R d K)
    (Y:∀i,R.family.label (d i))(turn:Fin n→Motion)(i:Fin n)(same:d i=4)

def input (r s:ℝ):(Z).Coeff:=castField R same (bid R d N per file Y turn r (s:ℂ) i)

def turned:(Z).Coeff:=castField R same
  (Motion.patch (R.family.labels.level (d i)) (turn i)
    ((file.A N per i).symm (fitted R (d i) (file.station i) N per (Y i))))

theorem seat (simple:G.Simple)(r:ℝ)(rp:0<r)(s:ℝ)(p:ℂ →L[ℝ] ℝ)(j:(Z).Index)(nonunit:j≠0):
    p (input R d N per file Y turn i same r s j)=
      income (K:=K) R N per r s * p (turned R d N per file Y turn i same j):=by
  have kernel:=sheetIncome R simple (K:=K) (N:=N) (per:=per) same
    (bid R d N per file Y turn r (s:ℂ) i)
    (Motion.patch (R.family.labels.level (d i)) (turn i)
      ((file.A N per i).symm (fitted R (d i) (file.station i) N per (Y i)))) r s
    (fun z=>WilsonPositionProgramTrialPublicJointFourVotedSheet.original R d N per file Y turn r rp (s:ℂ) i z) j nonunit
  change p (castField R same _ j)=_
  rw [kernel,←Complex.real_smul,p.map_smul]
  rfl

theorem active (simple:G.Simple)(r:ℝ)(rp:0<r)(s:ℝ)(p:ℂ →L[ℝ] ℝ)(a:Alma Z)(positive:sheet Z a≠0):
    amount (input R d N per file Y turn i same r s) p a=
      income (K:=K) R N per r s * p (turned R d N per file Y turn i same (sheet Z a)):=by
  have h:rankS a.val.2=0:=(WilsonPositionProgramTrialPublicJointFourLive.grades Z simple le_rfl a positive).2
  simpa only [amount,if_pos h] using seat R d N per file Y turn i same simple r rp s p _ positive

theorem size (simple:G.Simple)(r:ℝ)(rp:0<r)(s:ℝ)(p:ℂ →L[ℝ] ℝ):
    fieldSize (input R d N per file Y turn i same r s) p=
      |income (K:=K) R N per r s| * fieldSize (turned R d N per file Y turn i same) p:=by
  rw [WilsonPositionProgramTrialPublicJointFourSignedFrame.original Z simple,
    WilsonPositionProgramTrialPublicJointFourSignedFrame.original Z simple,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h:j=0
  · simp [strip,h]
  · simp only [strip,if_neg h,seat R d N per file Y turn i same simple r rp s p j h,abs_mul]

end YM.Integration.WilsonPositionProgramTrialPublicJointFourMixedIncome
