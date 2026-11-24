import YM.Integration.WilsonPositionProgramTrialPublicJointCapSurvey
import YM.Integration.WilsonOriginalPivotWardSurvey

/-! The genuinely placed high survey, tested at a lower field horizon, is an
admissible lower source at every original position. Its true rank suspension
on the common finite tree is the one of the incoming lower basis field. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointCapFiling
open Function Lattice Wilson RG Labels Source Source.Drops PertExtension PertExtension.Orb XSpace PowerSeries
open FormalOPE.RG10 FormalOPE.RG10.InversionTop FormalOPE.RG10.InversionWard
open FVA2 PhysicalNext.Repeat.Legato SlotEvaluation
open XSpace.Rose XSpace.Cirrus
open scoped Classical BigOperators
variable {G:Gauge}{lo hi:ℕ}(R:Run G)(W:Initialize G)(le:lo≤hi)
local notation "F_" h:max=>R.family.labels.level h

def sectionAt :SectionData (F_ lo):=
  (WilsonPositionProgramTrialPublicJointCapSurvey.original (W.surveys hi) (F_ lo) le).choose

theorem issued :
    (sectionAt R W le).Sound W.hol ∧ Bid.pop (sectionAt R W le) ∧
    ∀(p:Label G lo)(U:CoverConfig G),(sectionAt R W le).evaluate ((F_ lo).coords p) U=
      read (expand hi ((W.surveys hi).reading U)) p.val:=
  (WilsonPositionProgramTrialPublicJointCapSurvey.original (W.surveys hi) (F_ lo) le).choose_spec

theorem original (p:Label G lo)(U:CoverConfig G):
    (sectionAt R W le).evaluate ((F_ lo).coords p) U=
      (WilsonOriginalPivotWardSurvey.sectionAt R W hi).evaluate
        ((F_ hi).coords (raiseLabel G le p)) U:=by
  rw [(issued R W le).2.2,(WilsonOriginalPivotWardSurvey.issued R W hi).2.2]
  rfl

theorem placed (p:Label G lo){s:Side}(x:Site s)(U:Config G s):
    (sectionAt R W le).places ((F_ lo).coords p) x U=
      (WilsonOriginalPivotWardSurvey.sectionAt R W hi).places
        ((F_ hi).coords (raiseLabel G le p)) x U:=
  original R W le p (expandAt x U)

theorem sampled (P:Period)(T:P.Tree)(x:P.Sites)(i:(F_ lo).Index):
    Bare.scalar (G:=G) T (X^((F_ lo).grades i).2)*
      Bare.raw T (W.surveys hi) x ((F_ lo).basis i).val=
      BareOrb.stencil T (fieldAt (sectionAt R W le) i x):=by
  let p:Label G hi:=raiseLabel G le ((F_ lo).basis i)
  have grade:p∈Labels.Grade ((F_ lo).grades i):=by
    apply (pure_grade _ _).mpr
    exact (pure_grade _ _).mp ((F_ lo).pure i)
  have raw:=Bare.raw_calculation T (W.surveys hi) x (F_ hi) _
    (WilsonOriginalPivotWardSurvey.issued R W hi)
    ((F_ lo).grades i).1 ((F_ lo).grades i).2 grade
  have real (v):(WilsonOriginalPivotWardSurvey.sectionAt R W hi).places ((F_ hi).coords p) x (T.links v)=
      Complex.ofRealCLM (fieldAt (sectionAt R W le) i x (T.links v)):=by
    rw [show p=raiseLabel G le ((F_ lo).basis i) from rfl,←placed R W le,(F_ lo).coords_basis]
    exact (scalar_real (issued R W le).1).symm
  simp_rw [real] at raw
  have polynomial:p.val=((F_ lo).basis i).val:=rfl
  rw [polynomial] at raw
  simpa [Bare.scalar,BareOrb.stencil,TreeFormal.enter,Function.comp_def] using raw

end YM.Integration.WilsonPositionProgramTrialPublicJointCapFiling
