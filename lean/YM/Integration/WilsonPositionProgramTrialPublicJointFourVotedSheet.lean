import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedSource

/-! Signed public input on the ordinary nonconstant angular labels. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourVotedSheet
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

theorem original {n:ℕ}(d:Fin n→ℕ){K:ℕ}(N per:ℕ)(file:Filed R d K)
    (Y:∀i,R.family.label (d i))(turn:Fin n→Motion)(r:ℝ)(rp:0<r)(t:ℂ)(i:Fin n)
    (b:(R.family.labels.level (d i)).Index):
    let F:=R.family.labels.level (d i)
    let g:=regulatorRun R.family N per K
    let τ:=(R.family.path.rep N per K).p.threshold
    bid R d N per file Y turn r t i b=((r:ℂ)^(d i))⁻¹*t*((g/τ)^(F.grades b).2:ℝ)*
      (Motion.patch F (turn i) ((file.A N per i).symm (fitted R (d i) (file.station i) N per (Y i)))) b:=by
  intro F g τ
  let a:=R.family.S.a K
  have an:(a:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (R.family.S.a_pos K).ne'
  have rn:(r:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr rp.ne'
  have ruler:(((a/r)^(d i):ℝ):ℂ)*((a:ℂ)^(d i))⁻¹=((r:ℂ)^(d i))⁻¹:=by
    push_cast
    rw [div_pow]
    field_simp
  change (((a/r)^(d i):ℝ):ℂ)*t*
    (((g/τ)^(F.grades b).2:ℝ)*(((a:ℂ)^(d i))⁻¹*
      (Motion.patch F (turn i) ((file.A N per i).symm (fitted R (d i) (file.station i) N per (Y i)))) b))=_
  rw [←ruler]
  ring

theorem active {n:ℕ}{K:ℕ}(N per:ℕ)(file:Filed R (fun _:Fin n=>4) K)
    (simple:G.Simple)(Y:Fin n→R.family.label 4)(turn:Fin n→Motion)(r:ℝ)(rp:0<r)(t:ℂ)(i:Fin n)
    (a:Alma (R.family.labels.level 4))(live:sheet (R.family.labels.level 4) a ≠ 0)(p:ℂ →L[ℝ] ℝ):
    let F:=R.family.labels.level 4
    let g:=regulatorRun R.family N per K
    let τ:=(R.family.path.rep N per K).p.threshold
    amount (bid R (fun _:Fin n=>4) N per file Y turn r t i) p a=
      p (((r:ℂ)^4)⁻¹*t*((g/τ)^2:ℝ)*
        (Motion.patch F (turn i) ((file.A N per i).symm (fitted R 4 (file.station i) N per (Y i)))) (sheet F a)):=by
  intro F g τ
  have kind:=WilsonPositionProgramTrialPublicJointFourLive.grades F simple le_rfl a live
  have flat:rankS a.val.2=0:=kind.2
  rw [amount,if_pos flat,original R (fun _:Fin n=>4) N per file Y turn r rp t i (sheet F a)]
  change p (_*t*(_^(F.grades (sheet F a)).2:ℝ)*_)=_
  have degree:(F.grades (sheet F a)).2=2:=congrArg Prod.snd kind.1
  rw [degree]

end YM.Integration.WilsonPositionProgramTrialPublicJointFourVotedSheet
