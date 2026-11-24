import YM.Integration.WilsonPositionProgramTrialPublicJointFourMixedFitted

/-! Compare the deposited report with the original law, at its elected mixed leg. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourMixedDeposit
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
open WilsonPositionProgramTrialPublicJointFourSignedInput (income)
open WilsonPositionProgramTrialPublicJointFourMixedIncome (input turned)
open WilsonPositionProgramTrialPublicJointFourSignedFitted (coefficient)
open WilsonOriginalPublicTrialPhaseFourDictionary (seat Kept)
local notation "F₀" => R.family.labels.level 4

open WilsonPositionProgramTrialPublicJointFourMixedIncome (castField)

private theorem restored {h:ℕ}(same:h=4)(g:ℝ)(v:(R.family.labels.level h).Coeff):
    castField R same (vector (R.family.labels.level h) g v)=vector F₀ g (castField R same v):=by
  subst h
  rfl

def actual {h f K:ℕ}(same:h=4)(fit:4<D)(k m N per:ℕ)(T:SectionData F₀)
    (r s:ℝ)(A:Arm R h N per f K)(q:ℕ):(F₀).Coeff:=
  let wage:=castField R same (amounts R h K N per r (s:ℂ) (coords R A))
  let phase (p:ℂ→L[ℝ]ℝ)(j:(F₀).Index):=reading q (regulatorRun R.family N per m)
    (accrued R fit m K N k (Shrine (plate T fit) (written F₀ wage p)) (seat F₀ j).val)
  WilsonPositionProgramTrialPublicJointFourSignedComplex.field F₀ (phase Complex.reCLM) (phase Complex.imCLM)

theorem filed {n f K:ℕ}(grade:Fin n→ℕ)(i:Fin n)(same:grade i=4)(fit:4<D)(k m N per:ℕ)(T:SectionData F₀)
    (file:Filed R grade K)(Y:∀l,R.family.label (grade l))(turn:Fin n→Motion)(r s:ℝ)
    (A:Arm R (grade i) N per f K)(placed:A.w=(file.A N per i).symm
      (fitted R (grade i) (file.station i) N per (Y i)))(oriented:(A.s,A.b)=turn i)(q:ℕ):
    actual R same fit k m N per T r s A q=
      WilsonPositionProgramTrialPublicJointFourMixedFitted.field R fit k T m N per grade file Y turn r s i same q:=by
  have pay:castField R same (amounts R (grade i) K N per r (s:ℂ) (coords R A))=
      vector F₀ (regulatorRun R.family N per K) (input R grade N per file Y turn i same r s):=by
    rw [WilsonPositionProgramTrialPublicJointGroundVoted.chosen R grade N per file Y turn r (s:ℂ) i A placed oriented]
    exact restored R same _ _
  unfold actual
  rw [pay]
  rfl

end YM.Integration.WilsonPositionProgramTrialPublicJointFourMixedDeposit
