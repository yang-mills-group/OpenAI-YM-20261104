import YM.OPE.Compatible.Silva.Stylus
/-!
# tilted conditional Born. laws, along the centers
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side} {p:Clip}{R:PathData G}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val) (X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "W!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "Z!" => AxisChart G X!
variable (g:Bid.Dir G c→ AxisChart G (forest S.ratio he))
local notation "Qµ"=> Blocx S he H
local notation "P!" => Keys G X.Free
local notation "J!" => Keys G (Blocx S he H)
def valleyK : P!→L[ℝ] J!:= (FetchS S he H G) ∘L ( ContinuousLinearMap.snd ℝ _ _ ∘L (fderiv ℝ (viewS (cabin g)) 0 ∘L (rayS H X G)))
open Pilot
lemma valleyX (x: P!): valleyK S he H X g x=FetchS S he H G (fieldT (cabin g) (cloak H (X.rollX x))).2:= rfl
def Climb (M:P!→L[ℝ] J!): (P! × J!)≃ₗ[ℝ] (P! × J!) where
    toFun p:=(p.1,M p.1+p.2)
    invFun p:=(p.1,p.2-M p.1)
    map_add' u v:=Prod.ext rfl (by simp;abel)
    map_smul' a b:= Prod.ext rfl (by simp [smul_add])
    left_inv p:= by simp
    right_inv p:= by simp
def Tight : (P! × J!)≃L[ℝ] Keys G (stroll S he H X).Free:= (Climb S he H X (valleyK S he H X g)).toContinuousLinearEquiv.trans (Pilot.drinks V! G).symm
lemma tight_show (x:P!)(y:J!): Tight S he H X g (x,y)= (Pilot.drinks V! G).symm (x,valleyK S he H X g x + y):=rfl
lemma tight_p (x:P!)(y:J!): prL V! G (Tight S he H X g (x,y))=x ∧ prR V! G (Tight S he H X g (x,y))= valleyK S he H X g x+y:= Prod.mk.inj (show Pilot.drinks V! G ((Pilot.drinks V! G).symm _)=(x,_) from (Pilot.drinks V! G).apply_symm_apply (x,valleyK S he H X g x+y))
variable (U:Boxes G S.patch S.kernel) {L:Matrix (Body 1 f) (Body 1 c) ℝ}{B:Bed} (h:licensed S he U p R L B g) (t:S.Choices)
include t h
lemma tight_ray (x:P!)(y:J!): lamps S he H X G (Tight S he H X g (x,y))=fieldT (cabin g) (rayS H X G x)+(0,EchoV S he H G y):=by
     obtain ⟨ha,hb⟩:= tight_p S he H X g x y; let K:=fieldT (cabin g) (cloak H (X.rollX x)); rw [shines,ha,hb, map_add,valleyX, echoFetch S he H K.2 (fun i=>congr_arg Prod.snd (knowV S he H U h t i (X.rollX x)))]; apply Prod.ext
     · have ht :=viewer t h.2.1; rw [Prod.fst_add, show (fieldT _ _).1=rayS H X G x from ht.rim _, add_zero]
     rfl
open PertExtension Series ScriptJ GaussianScore Work.F05
lemma ttl : ∃ A : Law J!,∀ x y: J!, A.P x y= iteratedFDeriv ℝ 2 (pane X! t p R) 0 ![(0,EchoV S he H G x),(0,EchoV S he H G y)]/4:=by
      let W:= iteratedFDeriv ℝ 2 (pane X! t p R) 0; let T:=ContinuousLinearMap.inr ℝ (Bid.Dir G c) Z! ∘L (EchoV S he H G); let Z(a b:J!):= W ![T a,T b]/4
      have hm(u v):Z u v=Z v u:=congr_arg (fun x:ℝ=>x/4) (Work.F03.hessian_symmetric ((viewer t h.2.1).origin.of_le le_top) _ _)
      have hp (a:J!):∃ A:Dual' J!,Z a=A:=by
           let K:= (W.curryLeft (T a)).curryLeft ; refine ⟨{toFun:=Z a,map_add':=?_,map_smul':=?_},rfl⟩
           · intro b c; change K (T (b+c)) ![]/4= _; rw [map_add,map_add,_root_.add_apply,add_div];rfl
           intro u x; change K (T (u • x)) ![]/4= u*_;rw [map_smul, map_smul,_root_.smul_apply,smul_eq_mul,mul_div_assoc];rfl
      obtain ⟨A,hA⟩:= giraffe_addendum hp hm; refine ⟨Libra.giraffe A (fun x y=>by rw [hA,hA]; exact hm ..) ?_,hA⟩
      intro u hu; rw [hA]; unfold Z; change 0 < W ![(0,EchoV S he H G u),(0,EchoV S he H G u)]/4; apply div_pos _ (by norm_num); let v:=EchoV S he H G u; let P:=countingBasis X! G; let w:=cash P v; have hf:w≠0:=by intro hh; have ha:v=0:=P.equivFun.injective (hh.trans (map_zero P.equivFun).symm); exact hu (funext fun i=> show u i=0 from (echoIn S he H u i).symm.trans (congr_fun ha _))
      exact ((tollY S he U h t v v).symm ▸ show 0 < w ⬝ᵥ (FUND S he U*ᵥ w) from by rw [←star_trivial w]; exact (ulk_force S he U).dotProduct_mulVec_pos (star_ne_zero.mpr hf)) -- star rw
omit h t
-- generic formulation no choices: Law paying SPEC matrix; all moments materialized
abbrev Roomy (D:Law J!) : Prop:= ∀ x y,D.P x y=(dotProduct (cash (countingBasis X! G) (EchoV S he H G x)) (FUND S he U *ᵥ cash (countingBasis X! G) (EchoV S he H G y)))/4
include h t
lemma roomed : ∃ C: Law J!, Roomy S he H U C:=by
      obtain ⟨D,hD⟩:=ttl S he H g U h t; exact ⟨D,fun x y=>by rw [hD,tollY S he U h t]⟩
end YM.OPE.Cascade.Rill
