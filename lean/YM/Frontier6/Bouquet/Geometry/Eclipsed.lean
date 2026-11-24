import YM.Frontier6.Bouquet.Anise.Career

/-! Split around any baby subspace for cylindrical operations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {X:Type*}{P Q R:Place}
lemma on_budget [FiniteDimensional ℝ P]{x:Room}: ‖ontoSpace P x‖≤‖x‖:=by
    letI:=FiniteDimensional.complete ℝ P; exact P.norm_orthogonalProjectionOnto_apply_le x -- name?
lemma on_blank [FiniteDimensional ℝ P]{x:Room}(h:x∈Pᗮ): ontoSpace P x=0:= by
    letI:=FiniteDimensional.complete ℝ P; exact orthogonalProjectionOnto_eq_zero_iff.mpr h
lemma on_drop [FiniteDimensional ℝ P]{x:Room} : x-(ontoSpace P x).val∈Pᗮ:= by letI:=FiniteDimensional.complete ℝ P; exact sub_starProjection_mem_orthogonal _
lemma on_lower [FiniteDimensional ℝ P][FiniteDimensional ℝ Q] (h:P≤Q)(x:Room) : ontoSpace P x=ontoSpace P ((ontoSpace Q x).val):=by
    apply sub_eq_zero.mp; rw [← map_sub]; exact on_blank ((orthogonal_le h) on_drop)
def ledge [FiniteDimensional ℝ Q](h:P≤Q) :P→L[ℝ] Q:= by letI:=finiteDimensional_of_le h; exact insideCL h
def floorOf (P:Place)(Q:Place) [FiniteDimensional ℝ P]: Q→L[ℝ] P:= ontoSpace P ∘L Q.subtypeL
namespace Tandem
variable [FiniteDimensional ℝ P][FiniteDimensional ℝ Q][FiniteDimensional ℝ R] (h:Tandem P Q R) (x:P) (y:Q)
lemma of_left :floorOf P R (insideCL h.lft x)=x:= on_home x
lemma of_right :floorOf P R (insideCL h.rgt y)=0:= on_blank (h.orth y.property)
lemma canonical (p:P)(q:Q): together h (p,q)= insideCL h.lft p +insideCL h.rgt q:=rfl
lemma apart (r:R): together h (floorOf P R r,floorOf Q R r)=r:=by
    obtain ⟨x,y,hx⟩:= h.assembled r; rw [←(Subtype.ext hx : together h (x,y)=r), canonical h x y, map_add,map_add,h.of_left,h.of_right,h.symm.of_left,h.symm.of_right,add_zero,zero_add]; exact rfl
lemma knows_left : together h (x,y)=forward h.rgt (insideCL h.lft x) y:=rfl
lemma knows_right : together h (x,y)=forward h.lft (insideCL h.rgt y) x:=add_comm ..
lemma lt_norm (x:R): ‖floorOf P R x‖≤‖x‖:=on_budget (P:=P)
lemma eclipse (x:R): x-insideCL h.rgt (floorOf Q R x)=insideCL h.lft (floorOf P R x):=by nth_rw 1 [← h.apart x]; rw [canonical,add_sub_cancel_right]
end Tandem
-- slices
variable [FiniteDimensional ℝ P][FiniteDimensional ℝ Q] (h:P≤Q) (f:Full Q)
def centerless: Q→L[ℝ] Q:=ContinuousLinearMap.id ℝ Q-insideCL h ∘L floorOf P Q
lemma centerless_eq : centerless h= insideCL (loft_le : Loft Q P≤Q) ∘L floorOf (Loft Q P) Q:= by ext1 x; exact (attendance h|>.symm).eclipse x
lemma centerless_traces (i: P): centerless h (insideCL h i)=0:= by rw [centerless_eq, ContinuousLinearMap.comp_apply,(attendance h|>.symm).of_right i,map_zero]
lemma centerless_paths (x:Loft Q P):centerless h (insideCL loft_le x)=insideCL loft_le x:=by rw [centerless_eq,ContinuousLinearMap.comp_apply, (attendance h|>.symm).of_left]
lemma centerless_mem (x:Q): (centerless h x).val∈ Pᗮ:= by rw [centerless_eq]; exact loft_orth (floorOf (Loft Q P) Q x).property
lemma centerless_future (x:Q) (y:P): forward h (centerless h x) y=x- insideCL h (floorOf P Q x)+insideCL h y:= rfl
lemma centerless_self (x:Q): forward h (centerless h x) (floorOf P Q x)=x:=by rw [centerless_future,sub_add_cancel]
end YM.Frontier6.Bouquet
