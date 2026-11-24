import YM.Integration.WilsonMeasuredSignedActionCourse
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionAverage
open Function Filter Finset Labels Extra.Histories
open WilsonMeasuredSignedActionCourse
open scoped BigOperators Classical
variable {G:Gauge}(F:Frame G 4)
def pool (v:F.Coeff):F.Coeff:=∑s:Signed,F.act s.ortho (v+star v)
def cost:ℝ:=(Fintype.card Signed:ℝ)*Motion.orbitCost F*2

private theorem spin (g:Signed)(x:F.Coeff):F.act g.ortho (pool F x)=pool F x:=by
  unfold pool
  rw [map_sum]
  calc ∑s:Signed,F.act g.ortho (F.act s.ortho (x+star x)) =
      ∑s:Signed,F.act (g*s).ortho (x+star x):=by
        apply Finset.sum_congr rfl
        intro s _
        rw [show (g*s).ortho=g.ortho*s.ortho from map_mul Signed.inclusionO ..,Frame.act_mul]
    _ = _:=Equiv.sum_comp (Equiv.mulLeft g) (fun s:Signed=>F.act s.ortho (x+star x))

private theorem real (x:F.Coeff):star (pool F x)=pool F x:=by
  rw [pool,star_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [←Motion.act_conj]
  simp [add_comm]

theorem held (x:F.Coeff):fixed F (pool F x):=by
  rintro ⟨s,b⟩
  cases b <;> simp only [Motion.patch,spin,if_false,if_true,real,Bool.false_eq_true]

theorem costs (x:F.Coeff):F.coeffSize (pool F x) ≤ cost F*F.coeffSize x:=by
  have same:F.coeffSize (star x)=F.coeffSize x:=by simp [Frame.coeffSize]
  have one (s:Signed):F.coeffSize (F.act s.ortho (x+star x))≤Motion.orbitCost F*(2*F.coeffSize x):=by
    have h:=Motion.patch_cost F (s,false) (x+star x)
    have add:=Size.add F x (star x)
    rw [same,←two_mul] at add
    exact h.trans (mul_le_mul_of_nonneg_left add (zero_le_one.trans (Motion.orbitCost_one_le F)))
  calc _ ≤ _:=Size.finite F _ _
    _ ≤ ∑_s:Signed,Motion.orbitCost F*(2*F.coeffSize x):=Finset.sum_le_sum (fun s _=>one s)
    _ = _:=by simp [cost];ring

theorem linear {A:F.Coeff ≃ₗ[ℂ] F.Coeff}
    (actual:∀y w,Motion.patch F y (A w)=A (Motion.patch F y w))(x:F.Coeff):
    A (pool F x)=pool F (A x):=by
  have bar:star (A x)=A (star x):=by
    simpa only [Motion.patch,if_true,show (1:Signed).ortho=1 from map_one Signed.inclusionO,
      Frame.act_one] using actual (1,true) x
  have turned (g:Signed)(v:F.Coeff):F.act g.ortho (A v)=A (F.act g.ortho v):=actual (g,false) v
  simp only [pool,map_sum,←turned,bar,map_add]

theorem sub (x y:F.Coeff):pool F (x-y)=pool F x-pool F y:=by
  have input:(x-y)+star (x-y)=(x+star x)-(y+star y):=by rw [star_sub];abel
  simp only [pool,input,map_sub,Finset.sum_sub_distrib]

theorem core (x:F.Coeff):F.core (pool F x)=pool F (F.core x):=by
  have act (s:Signed)(v:F.Coeff):F.core (F.act s.ortho v)=F.act s.ortho (F.core v):=
    (Motion.core_patch F (s,false) v).symm
  have sum (f:Signed→F.Coeff):F.core (∑s,f s)=∑s,F.core (f s):=by
    funext i
    by_cases z:i=0 <;> simp [Frame.core,z,Finset.sum_apply]
  have part:F.core (x+star x)=F.core x+star (F.core x):=by
    funext i
    by_cases z:i=0 <;> simp [Frame.core,z]
  simp only [pool,sum,act,part]

end YM.Integration.WilsonMeasuredSignedActionAverage
end
