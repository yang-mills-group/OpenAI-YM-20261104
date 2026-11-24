import YM.Integration.WilsonVacuumPreResetPrunedBirth
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Macrame

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPrunedBirthCell
open Function Set Lattice RG Wilson Precision Ovens Ovens.Pipes WilsonStartup WilsonStartup.Start
open Progress.DirectedRecipe Progress.DirectedRecipe.Rack RG01Estimate
open Further.PhysicalPeriodLimitF933 Macrame WilsonVacuumPreResetPrunedBirthSites
open scoped Classical BigOperators

variable {G:Gauge}{n N:Side}{M:ℕ}

theorem field (W:PathData G)(c:Clip)(P:BudgetPoint)(β:ℝ)(u:Site n×Shapes)(A:Config G n):
    (filed n W c P β).activities.E (roster G n u) A=weight c β*residual G (key u).positive A:=by
  change stuff (upE (dictionary G n)) (payload c P G n β).regular
    (upE (dictionary G n) (Padded.index (Sum.inl (key u):Sheet n))) A=_
  rw [stuffed]
  simp [payload,written,Key.accrual_def]

variable (D:Window n N M)

private def vertices (a:PlaqAxes):Finset Cover:=
  {0,step a.val.1,step a.val.1+step a.val.2,step a.val.2}

private lemma rooted {k:Side}(x:Site k)(s:Signed)(a:PlaqAxes):
    (key (x,(s,a))).skin=(vertices a).image (fun v=>wrap k (s.act v)+x):=by
  simp [Key.skin,Key.root,Key.native,WilsonVacuumPreResetPrunedBirthSites.key,affine,
    four_visit,vertices,Finset.image_insert,←wrap_signed]

theorem footprint (u:Site N×Shapes):
    (key (D.cut u.1,u.2)).skin=(key u).skin.image D.cut:=by
  rcases u with ⟨x,s,a⟩
  rw [rooted,rooted,Finset.image_image]
  apply Finset.image_congr
  intro v hv
  change wrap n (s.act v)+D.cut x=D.cut (wrap N (s.act v)+x)
  rw [add_comm _ (D.cut x),add_comm _ x]
  exact (D.port x (s.act v)).symm

private lemma displacement (x:Site N)(v:Step):
    D.cut (x+(if v.neg then v.vec else 0))=D.cut x+(if v.neg then v.vec else 0):=by
  cases v.neg <;> simp [D.uniform]

theorem face (u:Site N×Shapes):
    (D.cut (key u).positive.1,(key u).positive.2)=(key (D.cut u.1,u.2)).positive:=by
  rcases u with ⟨x,s,a⟩
  refine Prod.ext ?_ rfl
  simp [key,Key.positive,Key.native,Key.root,Face.send,Face.lower,atFace,affine,displacement]

theorem measured (W:PathData G)(c:Clip)(P:BudgetPoint)(β:ℝ)(u:Site N×Shapes)(A:Config G n):
    (filed N W c P β).activities.E (roster G N u) (D.links A)=
    (filed n W c P β).activities.E (roster G n (D.cut u.1,u.2)) A:=by
  rw [field,field,←face D u]
  apply congrArg (weight c β*·)
  exact congrArg (surplus (G:=G)) (D.traveller A (key u).positive.1 (square (key u).positive.2.val.1 (key u).positive.2.val.2))

end YM.Integration.WilsonVacuumPreResetPrunedBirthCell
