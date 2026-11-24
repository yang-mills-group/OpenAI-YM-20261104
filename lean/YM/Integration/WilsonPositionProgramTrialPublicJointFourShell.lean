import YM.Integration.WilsonPositionProgramTrialPublicJointFourVariables
import YM.Integration.WilsonPositionProgramTrialPublicJointSourceProjected

/-! At horizon four the Maxwell equation removes no simple-gauge scalar or
tensor in the actual registered label space. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourShell
open Function Finset Labels Maxwell Tensor XSpace
open WilsonOriginalPublicFigureWick (remainder)
open scoped Classical BigOperators
variable {G:Gauge}
def solution (A:Labels.Taylor G 0):Shell G 0:=by
  refine ⟨takeCurl A,closedCurl A,?_⟩
  intro b x
  have constant (a:Axis):diagonal (takeCurl A a b)=fun _:E4=>takeCurl A a b (fun t:Fin 0=>Fin.elim0 t):=by
    funext y
    apply congrArg (takeCurl A a b)
    funext t
    exact Fin.elim0 t
  change (∑a:Axis,fderiv ℝ (diagonal (takeCurl A a b)) x (YM.basis a))=0
  simp_rw [constant]
  simp

theorem represented (A:Labels.Taylor G 0):gaugeJet (solution A)=A:=potential_recover A

variable {h:ℕ}(F:Frame G h)(simple:G.Simple)(cap:h≤4)
include F simple cap
theorem faithful:Injective (observable G h):=by
  intro p q eq
  have null:observable G h (p-q)=0:=by rw [map_sub,eq,sub_self]
  have known:(p-q).val=0:=by
    apply Labels.eval_ext
    intro A
    let u:TaylorTower G:=Pi.single 0 (solution (A 0))
    have fit:(fun t=>gaugeJet (u t)) 0=A 0:=by
      change gaugeJet (Pi.single 0 (solution (A 0)) 0)=A 0
      rw [Pi.single_eq_same,represented]
    calc
      read A (p-q).val=read (fun t=>gaugeJet (u t)) (p-q).val:=
        WilsonPositionProgramTrialPublicJointFourVariables.original F simple cap _ _ _ fit.symm
      _=0:=ideal_meaning.mp null u
      _=read A 0:=(map_zero _).symm
  exact sub_eq_zero.mp (Subtype.ext known)

theorem original (W:Initialize G)(v:F.Coeff):remainder W F v=0:=by
  apply faithful F simple cap
  rw [map_zero]
  exact WilsonOriginalPublicFigureWick.invisible W F v

end YM.Integration.WilsonPositionProgramTrialPublicJointFourShell
