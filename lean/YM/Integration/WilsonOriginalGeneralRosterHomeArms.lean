import YM.Integration.WilsonOriginalGeneralRosterFiledIncome
import YM.Integration.WilsonOriginalPhysicalFruitDose
import YM.Integration.WilsonOriginalPublicNodalDeployedVote

/-! The announced coefficient of one moved campus arm carries exactly the
engineering factor for its own physical scale. The filed vote has already
restored the inverse mesh power, including on scalar components. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeArms
open Finset Lattice Wilson RG Source Labels Marker QuadraticLocal.Affinity MergeProof.Accent
open PhysicalNext.Repeat.Legato Pert.Asymptotics Extra.Histories Motion RG16 RG16.Literal
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonOriginalPublicNodalDeployedVote (deployed)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "C" => R.family

def amplitude (d K:ℕ)(radius:ℝ)(t:ℂ):ℂ:=((((C).S.a K/radius)^d:ℝ):ℂ)*t

def component (d K:ℕ)(radius:ℝ)(t:ℂ)(p:ℂ→L[ℝ]ℝ):ℂ→L[ℝ]ℝ:=
  p.comp (ContinuousLinearMap.mul ℝ ℂ (amplitude R d K radius t))

theorem source (d K N per:ℕ)(radius:ℝ)(t:ℂ)(v:(C).label d):
    amounts R d K N per radius t v=(amplitude R d K radius t) •
      deployed R d K (N,per) (((((C).S.a K:ℂ)^d)⁻¹) • v):=by
  funext i
  simp only [amounts,amplitude,WilsonOriginalPublicTrialFigure.amount,WilsonAddressedTrialPivotUnits.row,
    deployed,WilsonOriginalPublicNodalDeployedVote.vector,WilsonPositionProgramReportedField.entire,
    gMap,Frame.scaled_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem sectionAt (d K N per:ℕ)(radius:ℝ)(t:ℂ)(v:(C).label d)(phase:ℂ→L[ℝ]ℝ):
    written ((C).labels.level d) (amounts R d K N per radius t v) phase=
      written ((C).labels.level d) (deployed R d K (N,per) (((((C).S.a K:ℂ)^d)⁻¹) • v))
        (component R d K radius t phase):=by
  rw [source]
  funext i
  simp only [written,component,ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',
    Pi.smul_apply,smul_eq_mul]

theorem original {n N per f K req power tag:ℕ}(d:Fin n→ℕ){credit:ℝ}{fk:f≤K}{cut:K≤N}
    (panel:Panel R d N per f K fk cut req power tag credit)(file:Filed R d K)
    (stations:panel.slot=file.station)(axes:panel.axis=file.A N per):
    let actual:=votes R d (N:=N) (per:=per) file panel.names panel.turn
    ∃arms:∀i,Arm R (d i) N per f K,
      (∀i,(arms i).Y=panel.names i ∧
        (arms i).w=(file.A N per i).symm (fitted R (d i) (file.station i) N per (panel.names i)) ∧
        (arms i).b=(panel.turn i).2 ∧ (arms i).s=(panel.turn i).1 ∧ (arms i).o=panel.loc i) ∧
      (∀i,actual i=(((((C).S.a K:ℂ)^(d i))⁻¹) • coords R (arms i))) ∧
      ∀(i:Fin n)(radius:ℝ)(t:ℂ)(phase:ℂ→L[ℝ]ℝ),
        written ((C).labels.level (d i)) (amounts R (d i) K N per radius t (coords R (arms i))) phase=
        written ((C).labels.level (d i)) (deployed R (d i) K (N,per) (actual i))
          (component R (d i) K radius t phase):=by
  intro actual
  choose arms names raw sign spin location priced budget using fun i=>WilsonReflectedMixedMasterAxes.placed R
    (panel.fixed i) (panel.turn i).1 (panel.turn i).2 (panel.loc i)
  have before i:(arms i).w=(file.A N per i).symm (fitted R (d i) (file.station i) N per (panel.names i)):=by
    rw [←axes,←stations];exact raw i
  have read i:actual i=(((((C).S.a K:ℂ)^(d i))⁻¹) • coords R (arms i)):=by
    change _= _ • Motion.patch _ ((arms i).s,(arms i).b) (arms i).w
    rw [sign i,spin i,before i];rfl
  exact ⟨arms,fun i=>⟨names i,before i,sign i,spin i,location i⟩,read,
    fun i radius t phase=>by rw [read i];exact sectionAt R _ _ _ _ _ _ _ _⟩

end YM.Integration.WilsonOriginalGeneralRosterHomeArms
end
