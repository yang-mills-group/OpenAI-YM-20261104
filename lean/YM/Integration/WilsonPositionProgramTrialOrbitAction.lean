import YM.Integration.WilsonPositionProgramTrialGaugeAction

/-! The genuine gauge-fixed action on the independent inversion, before any
coefficient is taken, is the local Wilson action on the reflected link space. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialOrbitAction
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart
open Function Finset FVA2 FVA2.Trans FVA2.Wilson FVA2.Wilson.FP Precision Inherit Push.Loops TreeBasis
open WilsonPositionProgramTrialSiteGauge (reporter link)
open WilsonPositionProgramTrialGaugeAction (siteLaw)
open scoped Classical BigOperators
variable (G : Gauge) (n : Side) (even : Even n.val)

def coordinates : Cone G n ≃ₗ[ℝ] Pert.Orb.Potential G n :=
  LinearEquiv.ofBijective (link G n even) ⟨fun _ _ h=>coverL_inj G n (congrArg Subtype.val h),by
    intro x
    exact ⟨fun i=>x.val i.val,Subtype.ext (own_image G n x.property)⟩⟩

theorem plate (A : Cone G n) (x : Site n) (p : PlaqAxes) :
    faceValue (assemble G n A) (x,p) = Pert.Orb.plaquette (link G n even A) x p.val.1 p.val.2 := by
  rw [assemble_exp]
  change faceValue (expLinks G _ (coverL G n A)) (x,p)=_
  unfold Pert.Orb.plaquette Pert.Orb.positiveLinks
  simp [faceValue,square,travel,Step.read,posDir,negDir,Step.vec,Step.used,expLinks,link,
    sub_eq_add_neg,add_comm,add_left_comm,add_assoc,mul_assoc]

theorem plaquettes (A : Cone G n) :
    pricing G n A = Pert.Orb.wilson (link G n even A) := by
  unfold pricing YM.Wilson.energy Pert.Orb.wilson
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [plate G n even A]
  let V (p : Axis×Axis):=G.price (Pert.Orb.plaquette (link G n even A) x p.1 p.2)
  change (∑p:PlaqAxes,V p.val)=_
  rw [←Finset.sum_subtype (p:=fun p:Axis×Axis=>p.1<p.2)
    (univ.filter fun p:Axis×Axis=>p.1<p.2) (fun p=>by simp) V,Finset.sum_filter]
  exact Fintype.sum_prod_type _

theorem original (A : Cone G n) :
    let R:=reporter G n even
    let good:=WilsonPositionProgramTrialSiteGauge.original G n even
    finances (Repoint.issue G (staple n) R good) (matchW R good (siteLaw G n)) A =
      Pert.Orb.action G n (coordinates G n even A) := by
  intro R good
  rw [WilsonPositionProgramTrialGaugeAction.original G n even A,plaquettes G n even A]
  rfl

end YM.Integration.WilsonPositionProgramTrialOrbitAction
