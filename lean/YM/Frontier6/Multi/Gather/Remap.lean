import YM.Frontier6.Multi.Gather.Anise
import YM.MergeProof.North.Harvest
/-! Relabel without distorting program, or further grouping.
Composition formula on reaped polynomial inclusion of the full preimage modes. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Finset Function Marker Extra.Trajectories Lattice Wilson RG Pressure Filter MeasureTheory Accent Ribbon
open Push Marker Source Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus Extra.Multi GridApprox.Nil
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {V O Modes : Type}[DecidableEq V][DecidableEq O][Fintype V][Fintype O]
variable {G:Gauge}{n:Side}
namespace Concentrate
set_option quotPrecheck false
variable (E:Concentrate V O)
def alongside (D:Concentrate O Modes) : Concentrate V Modes:= ⟨D.hit ∘ E.hit,E.seat ∘ D.seat,fun i=>by exact (congr_arg D.hit (E.parked _)).trans (D.parked i)⟩
lemma total [DecidableEq Modes][Fintype Modes](D:Concentrate O Modes) (b:(Bud Modes).Mode) : (E.alongside D).plena b=E.plena (D.plena b):= by apply Subtype.ext;ext i; simp only [plena,mem_filter,mem_univ,true_and]; rfl
lemma reaper [DecidableEq Modes][Fintype Modes](D:Concentrate O Modes) (X:Poly (Bud V)) : (E.alongside D).reap X=D.reap (E.reap X):=by ext1 p; change X.part _=X.part _; rw [total]

def identity (V:Type) : Concentrate V V:=⟨id,id,fun _=>rfl⟩
lemma reap_id (X:Poly (Bud V)) : (identity V).reap X=X:=by ext p; change X.part _=X.part p; congr 1; apply Subtype.ext; ext i; simp [plena,identity]

def relabel (F: V ≃ O):Concentrate V O:=⟨F,F.symm,F.right_inv⟩
variable (F: V ≃ O)
local notation "T"=>relabel F
local notation "r!"=>reap (relabel F)



def code : (Bud V).Mode≃(Bud O).Mode where
   toFun:= (T).span
   invFun:= (T).plena
   right_inv:= (T).reband
   left_inv i:=by apply Subtype.ext; ext j; simp only [plena,Concentrate.span,mem_filter,mem_univ,true_and]; exact Ribbons.mem_image_of_injective _ F.injective -- test
lemma cars (b:(Bud V).Mode) : (code F b).val= b.val.image F:=rfl
lemma assigned (X:Poly (Bud V)) (p:(Bud V).Mode): (r! X).part (code F p)=X.part p:=congr_arg X.part ((code F).left_inv p)
lemma reassigned (X:Poly (Bud V)) (p:(Bud O).Mode): (r! X).part p=X.part ((code F).symm p):=rfl
lemma recolor (p:(Bud V).Mode)(c:ℂ) : r! (Poly.send p c)=Poly.send (code F p) c:= by rw [Concentrate.harvest]; exact if_pos ((code F).left_inv p|>.symm : (T).Pays p)
lemma night : code F ((Bud V).quiet)=(Bud O).quiet:=by apply Subtype.ext; simp [cars,Census.quiet]
lemma plots (x y:Poly (Bud V)) : r! (x*y)=r! x*r! y:=by
    ext p; obtain ⟨p,rfl⟩:= (code F).surjective p; rw [assigned,Poly.part_mul,Poly.part_mul,← Equiv.sum_comp (code F)]; refine sum_congr rfl fun i _=>?_
    rw [← Equiv.sum_comp (code F)]; refine sum_congr rfl fun j _=>?_
    have hs: Poly.merges i j p↔ Poly.merges (code F i) (code F j) (code F p):=by
       unfold Poly.merges; simp only [cars,← Finset.image_union]; exact and_congr ((Finset.disjoint_image F.injective).symm) (Finset.image_injective F.injective|>.eq_iff.symm)
    by_cases hh:Poly.merges i j p <;>simp [← hs,hh,assigned]
lemma dawn : r! 1=1:=by ext p; obtain ⟨p,rfl⟩:=(code F).surjective p; rw [assigned,Poly.one_part,Poly.one_part, ← show _=(Bud O).quiet from night F]; simp
lemma powers (X:Poly (Bud V))(b:ℕ): r! (X^b)=(r! X)^b:=by induction b with
    | zero=> simp only [pow_zero]; exact dawn F
    | succ b ih=> rw [pow_succ, pow_succ,plots,ih]
lemma pass (X:Poly (Bud V)): r! (X.pass)=(r! X).pass:=by unfold Poly.pass; rw [map_sum,Fintype.card_congr F]; simp_rw [map_smul,powers]
lemma mach (L:V→ℂ) : r! (Mach (Bud V) L)=Mach (Bud O) (L ∘ F.symm):=by
   unfold Mach; rw [map_sum,← Equiv.sum_comp F]; refine sum_congr rfl fun i _=>?_; rw [recolor,comp_apply,Equiv.symm_apply_apply,show code F ((Bud V).fire i)=(Bud O).fire (F i) from (Subtype.ext (by rw [cars]; exact image_singleton ..))]
lemma rebate (X:Box n→Poly (Bud V))(s:Support n): r! (field X s)=field (r! ∘ X) s:=by
   
   have he(p:Finset (Box n)): r! (∏ i∈p,X i)=∏ i∈p,r! (X i):= by
      induction p using Finset.induction_on with
      | empty=> rw [prod_empty,prod_empty,dawn]
      | @insert i p hi ih=> rw [prod_insert hi,prod_insert hi,plots,ih];
   unfold field; rw [map_sum]; refine sum_congr rfl fun i _=>?_; unfold grid; split
   next h=> exact he _
   next h=> simp [map_zero]

lemma right_bar (A:Activities G n)(U:Config G n)(p:Box n) : r! (bar A (Bud V) U p)=bar A (Bud O) U p:=by
   unfold bar Poly.bead; change r! (Poly.send _ _)=Poly.send _ _; rw [recolor,night]

lemma partWorth (p:(Bud V).Mode)(w:V→ℝ) : Poly.toll w p=Poly.toll (w ∘ F.symm) (code F p):=by simp only [Poly.toll,cars, Finset.prod_image F.injective.injOn,comp_apply,Equiv.symm_apply_apply]
lemma born (o:V→Site n)(t:ℝ)(s:Support n)(X:Config G n→Poly (Bud V)) (h:Borne o s X t) : Borne (o ∘ F.symm) s (r! ∘ X) t where
   home _ _ hx hZ:= congr_arg (r!) (h.home _ _ hx hZ)
   turns σ U:= congr_arg (r!) (h.turns ..)
   me p:= h.me ((code F).symm p)
   scope U p hu:=by
     obtain ⟨q,rfl⟩:= (code F).surjective p; rw [comp_apply,assigned]; apply (h.scope U); intro hp; apply hu; rw [cars]; intro i hi; obtain ⟨i,hj,rfl⟩:=mem_image.mp hi; change o (F.symm (F i))∈ s; rw [F.symm_apply_apply]; exact hp hj

lemma vowed {w:V→ℝ}{b e c}{S:Modes→Support n}{P:Modes→ Config G n→Poly (Bud V)} (h:Towed w S P b e c) : Towed (w ∘ F.symm) S (fun i=>r! ∘ P i) b e c:=by
   obtain ⟨a,H,hA,h⟩:=h; refine ⟨a,H,hA,fun i=>?_⟩; obtain ⟨P',hQ,hB,hX⟩:=h i; refine ⟨P' ∘ (code F).symm,fun p=>hQ _,fun U p=>hB _ _,?_⟩; unfold wordsPrice; rw [← Equiv.sum_comp (code F)]; simp only [comp_apply,Equiv.symm_apply_apply,← partWorth]; exact hX

lemma unpacked {X:Config G n→Poly (Bud V)} {A:Rep G n}{o: V→Site n}{w:V→ℝ}{f' K e c} (h:Served A f' K X o w e c) : Served A (f' ∘ F.symm) (K ∘ F.symm) (r! ∘ X) (o ∘ F.symm) (w ∘ F.symm) e c:=by
   obtain ⟨H,P,h,hH,hP,rfl⟩:=h
   have ho(X:Config G n→Poly (Bud V))(he:∀ U,rises (X U)) (U): rises ((r! ∘ X) U):=by intro i; obtain ⟨p,rfl⟩:=(code F).surjective i; rw [comp_apply,assigned,cars,card_image_of_injective _ F.injective]; exact fun h=> he U p h
   have hv(X:Config G n→Poly (Bud V))(U) (h:(r! ∘ X) U≠0): X U≠0:=fun he=>h (by simp [he])
   refine ⟨fun i=>r! ∘ H i,fun i=> r! ∘ P i,⟨fun i=> ⟨?_,ho _ (h.exp i|>.2)⟩,fun i=>⟨?_,ho _ (h.flag i|>.2)⟩⟩,vowed F hH,vowed F hP,?_⟩ -- _ → ?_
   · exact ⟨born F _ _ _ _ (h.exp i|>.1.toBorne),fun U he=> (h.exp i|>.1.permits U (hv _ U he)),fun U=> by rw [comp_apply,← night F, assigned]; exact (h.exp i|>.1.sil U)⟩
   · exact ⟨born F _ _ _ _ (h.flag i|>.1.toBorne),fun U he=> (h.flag i|>.1.permits U (hv _ U he))⟩
   funext U; dsimp only [Function.comp,restore]; rw [map_smul,plots,pass,rebate,map_add,map_sum,mach];
   congr 2; apply congr_arg (field · _); funext p; dsimp only [Function.comp]; rw [map_add,map_add,right_bar,mach]; rfl
lemma gust_from {A:History G}{N p j:ℕ}(X:Config G (A.S.side N p)→Poly (Bud V))(hi:Integrable X (prior G _))(hN:j≤N):
    gust A N p N (E.reap ∘ X) j hN=E.reap ∘ gust A N p N X j hN:=by
    induction hN using Nat.decreasingInduction with
    | self=> rw [gust_base,gust_base]
    | of_succ i hj IH=> rw [gust_step _ _ _ _ _ hj, IH]; funext U; rw [comp_apply,gust_step _ _ _ _ _ hj]; unfold StepData.push; let L':= E.reap.restrictScalars ℝ; have he:= L'.integral_comp_comm (StepData.push_slice (A.levels.transition_mass i p (A.β N p (i+1))) U _ (gust_live A N _ _ _ hi hj)); simp_rw [L'.map_smul] at he; exact he
lemma expander {A:Rep G n} (X:V→ Config G n→ℂ): E.reap ∘ birth (Bud V) A X=birth (Bud O) A (fun i U=>∏ j∈E.fiber i,X j U):=by
    funext U; ext p; change ((birth (Bud V) A X) U).part (E.plena p)=_; unfold birth Mach; simp only [Poly.part_smul,pass_fire]; congr 1; rw [E.above]; apply prod_biUnion; intro i hi j hj hh; exact disjoint_left.mpr (fun k hx he=> hh (((mem_filter.mp hx).2).symm.trans ((mem_filter.mp he).2)))
end Concentrate
end YM.MergeProof.Canopies
