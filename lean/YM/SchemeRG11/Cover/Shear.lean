import YM.SchemeRG11.Cover.Breathe
import YM.SchemeRG11.Cover.Bloom
/-! Covariant stencil normaling, stem grading. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Haze
open MvPolynomial
variable {R S J I B : Type*} [CommRing R]
namespace Dose
variable (D:Dose I R)
def bend (z:I→R): Paper I R→ₐ[R] Paper I R:= aeval fun i=> X i+MvPolynomial.C (z i)
lemma bending(z:I→R)(i:I): bend z (X i)=X i+MvPolynomial.C (z i):=aeval_X ..
lemma bends(z:I→R)(u:I→R)(p:Paper I R): bend z (vent u p)=vent u (bend z p):=by
 induction p using MvPolynomial.induction_on with
 | C c=> rw [vent_C,map_zero, show bend z (C c)=C c from (bend z).commutes _,vent_C]
 | add a b ha hb=> rw [map_add,map_add,ha,hb,map_add,map_add]
 | mul_X a i h=> rw [vent_x,map_mul (bend z),map_add (bend z),map_smul,map_mul (bend z),bending,h, mul_add,map_add,vent_x,vent_l,vent_C,mul_zero,zero_add]; ring
lemma pour (z:I→R) (p:Paper I R): D.heat (bend z p)=bend z (D.heat p):=by
 induction p using MvPolynomial.induction_on with
 | C c=> rw [show bend z (C c)=C c from (bend z).commutes _,heat_C,show bend z (C c)=C c from (bend z).commutes _]
 | add a b ha hb=> rw [_root_.map_add,map_add,map_add,map_add,ha,hb]
 | mul_X a i h=>rw [map_mul (bend z),bending,mul_add,map_add,heat_x,mul_comm _ (C _),C_mul',map_smul,heat_x,h,map_add,map_mul,bending,bends,MvPolynomial.smul_eq_C_mul];ring
def arrow (w:J→I)(j:J) : Stem I R:= Finsupp.single (w j) 1
lemma reflow (z:I→R)(p:Paper I R): D.avg (bend z p)=MvPolynomial.aeval z (D.heat p):=by
 rw [D.avg_def,pour]; apply DFunLike.congr_fun (f:=(MvPolynomial.aeval (R:=R) (fun _:I=>(0:R))).comp (bend z)) ?_ (D.heat p); ext i
 rw [AlgHom.comp_apply,bending,map_add,aeval_X,zero_add,aeval_X,aeval_C];rfl
lemma rebase (w:J→I) (p:Paper J R) : rename w p = vary (arrow w) p:=by
 apply DFunLike.congr_fun ?_ p; ext j;rw [vary_X,rename_X,arrow,leaf,Finsupp.linearCombination_single,one_smul]
lemma migrate(w:J→I)(p:Paper J R) : D.heat (rename w p)=rename w ((D.pull (arrow w)).heat p):=by rw [rebase,light,rebase]
lemma reach(w:J→I)(u v:J): (D.pull (arrow w)).pulse u v=D.pulse (w u) (w v):=by
 unfold pull bed arrow; simp only [sense,Finsupp.linearCombination_single,one_smul,single_wind]
lemma strict (P Q:Dose I R)(H:∀ i j,P.pulse i j=Q.pulse i j): P=Q:=by obtain ⟨p,hp⟩:=P; obtain ⟨q,hq⟩:= Q; congr; exact _root_.funext fun i=> _root_.funext fun j=> H i j
end Dose
end YM.SchemeRG11.Haze
