import YM.OPE.Compatible.Kyoto.Yank
/-!
# complex field basis map. Work across Hermit coordinates pre-flow.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Dial
open Function Filter Module Set Finset WithLp
open scoped Topology ContDiff BigOperators Classical
variable {J I E F:Type}{h d:ℕ}{L:Filter I}{p:I→ℝ}
variable (D:Fin (d+1)→ℕ)
variable {t s u:ℝ}
open Yolk Pill
section
variable [Fintype J] (P:J→CanA D×CanA D)
noncomputable def Pique : (J→ℂ)→L[ℂ] BoxQ D:= LinearMap.toContinuousLinearMap {
       toFun i:= Garm D (Arco P i)
       map_add' x y:=by rw [map_add,map_add]
       map_smul' a x:=by
            simp_rw [bWire,Pi.smul_apply, map_sum,RingHom.id_apply, Finset.smul_sum]; refine sum_congr rfl fun i _=>?_ ; change Garm D _ = a • _; rw [VintQ,VintQ]; rw [← mul_smul]; rfl -- rw RHS? check
}
lemma Flare (x:J→ℂ): Pique D P x=Garm D (Arco P x):=rfl
lemma Fray (d:J): Pique D P (Pi.single d 1)= Garm D (P d):=by rw [Flare, Yolk.chordMem P d] -- decidable
end
section cope
variable [NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℂ E][NormedSpace ℂ F][NormedSpace ℝ E][NormedSpace ℝ F][IsScalarTower ℝ ℂ E][IsScalarTower ℝ ℂ F]
local notation "i'*"=>Complex.I
omit [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] in lemma Doom (T:E→L[ℂ] F)(P:E→L[ℝ] F)(h:∀ i,T i=P i): ‖T‖≤ ‖P‖:= by refine T.opNorm_le_bound (norm_nonneg _) (fun x=>?_); rw [h]; exact P.le_opNorm x
-- inverse symmetrize over C.Conven.
omit [IsScalarTower ℝ ℂ E] [NormedSpace ℝ E] in
private lemma Nqq (x:E): i'* • (i'* • x)= -x:=by rw [smul_smul,Complex.I_mul_I]; exact neg_one_smul ..
def MossR (p:F→L[ℝ] E) (x:F): E:=((1:ℂ)/2) • (p x- i'* • p (i'* • x))
variable [FiniteDimensional ℂ F]
omit [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] in
private lemma Mz (p:F→L[ℝ] E) (x:F): MossR p (i'* • x)= i'* • MossR p x:=by
       unfold MossR; rw [Nqq x,p.map_neg,smul_neg,sub_neg_eq_add]; rw [show i'* • ((1/2:ℂ) • _) = (1/2:ℂ) • (i'* • _) from smul_comm i'* _ _,smul_sub,Nqq,sub_neg_eq_add,add_comm]
noncomputable def Cloom (p:F→L[ℝ] E) : F→L[ℂ] E:= by
       have hf (a:ℝ)(x:F): MossR p (a • x)=a • MossR p x:=by
            unfold MossR; rw [smul_comm i'* a, smul_comm a ((1:ℂ)/2), map_smul, map_smul]
            apply congr_arg (fun x:E=> ((1:ℂ)/2) • x); rw [smul_sub,smul_comm i'* a]
       let f:F→ₗ[ℝ] E := {toFun:= MossR p, map_add' x y:= by unfold MossR; rw [map_add,smul_add,map_add,smul_add]; simp only [smul_sub,smul_add]; abel, map_smul':=hf}; refine LinearMap.toContinuousLinearMap {toFun:=f,map_add':=f.map_add,map_smul':=fun a x=>?_}
       change f (a • x)=a • f x
       refine (congr_arg (fun u=>f (u • x)) (Complex.re_add_im a).symm).trans ((show f ((↑a.re+ ↑a.im * i'*) • x)=(↑a.re+ ↑a.im * i'*) • f x from ?_).trans (congr_arg (fun u:ℂ=>u • f x) (Complex.re_add_im a)))
       rw [add_smul, add_smul,mul_smul,mul_smul]; rw [show (↑a.re:ℂ) • x=a.re • x from (RCLike.real_smul_eq_coe_smul ..).symm,show (↑a.im:ℂ) • (Complex.I • x)=a.im • (Complex.I • x) from (RCLike.real_smul_eq_coe_smul ..).symm,show (↑a.re:ℂ) • f x=a.re • f x from (RCLike.real_smul_eq_coe_smul ..).symm,show (↑a.im:ℂ) • (Complex.I • f x)=a.im • (Complex.I • f x) from (RCLike.real_smul_eq_coe_smul ..).symm]; rw[f.map_add, f.map_smul, f.map_smul,show f (i'* • x)=_ from Mz p x]; rfl
-- Moss estimate
lemma Dcout (Z:E→L[ℂ] F)(P:F→L[ℝ] E)(h:∀ i:F,Z (P i)=i):Z.comp (Cloom P)=ContinuousLinearMap.id ..:=by
       ext1 x; change Z (((1:ℂ)/2) • (P x-i'* • P (i'* • x)))=x; rw [map_smul,map_sub,map_smul,h,h,Nqq]; module -- test
lemma Dprice (P:F→L[ℝ] E):‖Cloom P‖ ≤ ‖P‖:=by
        refine (Cloom P).opNorm_le_bound (norm_nonneg _) ?_ ; intro i; change ‖((1:ℂ)/2) • (P i-i'* • P (i'* • i))‖≤_; rw [norm_smul, norm_div,norm_one, Complex.norm_ofNat]; have hx:= (P.le_opNorm i); have hz: ‖i'* • P (i'* • i)‖ ≤ ‖P‖*‖i‖:= by
           have hh:= P.le_opNorm (Complex.I • i); rwa [norm_smul, Complex.norm_I,one_mul] at * -- try
        linarith only [norm_sub_le (P i) (Complex.I • P (Complex.I • i)), hx,hz]
end cope
end YM.OPE.Dial
