import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedFrame

/-! Complex active angular fields with the original field-size norm. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedComplex
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

theorem stripped (F:Frame G 4)(v:F.Coeff):strip v=F.core v:=by
  funext j
  by_cases h:j=0 <;> simp [strip,Labels.Frame.core,Function.update,h]

theorem contraction (F:Frame G 4)(simple:G.Simple)(v:F.Coeff)(p:ℂ→L[ℝ]ℝ)(hp:∀z:ℂ,|p z|≤‖z‖):
    fieldSize v p≤F.coeffSize (F.core v):=by
  rw [WilsonPositionProgramTrialPublicJointFourSignedFrame.original F simple,Labels.Frame.coeffSize,stripped]
  exact Finset.sum_le_sum (fun _ _=>hp _)

theorem scaled (F:Frame G 4)(v:F.Coeff)(t:ℝ):
    F.coeffSize ((t:ℂ) • v)=|t| * F.coeffSize v:=by
  simp only [Labels.Frame.coeffSize,Finset.mul_sum,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]

def field (F:Frame G 4)(u w:F.Index→ℝ):F.Coeff:=F.core fun i=>(u i:ℂ)+(w i:ℂ)*Complex.I

theorem original (F:Frame G 4)(simple:G.Simple)(v:F.Coeff)(re im:F.Index→ℝ)(t E:ℝ)
    (ht:0≤t)(he:0≤E)
    (rr:∀j:F.Index,j≠0 → |re j-t*(v j).re|≤t*E*fieldSize v Complex.reCLM)
    (ii:∀j:F.Index,j≠0 → |im j-t*(v j).im|≤t*E*fieldSize v Complex.imCLM):
    F.coeffSize (field F re im-(t:ℂ) • F.core v) ≤
      (2*(Fintype.card F.Index:ℝ)*E)*F.coeffSize ((t:ℂ) • F.core v):=by
  classical
  let m:=F.coeffSize (F.core v)
  have mn:0 ≤ m :=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have rsize:fieldSize v Complex.reCLM ≤ m :=contraction F simple v _ Complex.abs_re_le_norm
  have isize:fieldSize v Complex.imCLM ≤ m :=contraction F simple v _ Complex.abs_im_le_norm
  have born:∀j:F.Index,‖(field F re im-(t:ℂ) • F.core v) j‖≤2*(t*E*m):=by
    intro j
    by_cases hj:j=0
    · subst j
      simpa [field,Labels.Frame.core] using (show 0≤2*(t*E*m) by positivity)
    · let z:ℂ:=(re j:ℂ)+(im j:ℂ)*Complex.I-(t:ℂ)*v j
      have e₁:= (rr j hj).trans (mul_le_mul_of_nonneg_left rsize (mul_nonneg ht he))
      have e₂:= (ii j hj).trans (mul_le_mul_of_nonneg_left isize (mul_nonneg ht he))
      have r:z.re=re j-t*(v j).re:=by simp [z,Complex.mul_re]
      have i:z.im=im j-t*(v j).im:=by simp [z,Complex.mul_im]
      have norm:=Complex.norm_le_abs_re_add_abs_im z
      rw [r,i] at norm
      change ‖(F.core (fun a=>(re a:ℂ)+(im a:ℂ)*Complex.I)) j-(t:ℂ)*(F.core v) j‖≤_
      simp only [Labels.Frame.core,LinearMap.coe_mk,AddHom.coe_mk,Function.update_of_ne hj]
      exact norm.trans (by linarith only [e₁,e₂])
  rw [scaled,abs_of_nonneg ht]
  calc
    _ ≤ ∑_j:F.Index,2*(t*E*m):=Finset.sum_le_sum fun j _=>born j
    _=_:=by simp [m];ring

end YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedComplex
