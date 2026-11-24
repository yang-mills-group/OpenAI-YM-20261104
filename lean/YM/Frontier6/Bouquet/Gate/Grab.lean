import YM.Frontier6.Bouquet.Geometry.Atlas
/-!
# Combinatorial support forests. Scar set $P \\ Q$ takes every pod crossing
 a refinement. Such a factor only used as a convergence regulator for proving
 compatibility, not the Taylor length. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Ensemble
open Function Set Finset MeasureTheory Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q R:Ensemble}{p q:Pod}
-- any enclosed pod (including singletons)
def enclosed (P:Ensemble) : Finset Pod:= (stages_finite P.Along).toFinset.filter fun p=>∃ q∈ P.choose, p≤q
lemma encloses : p∈ P.enclosed ↔ ∃ q∈P.choose,p≤q:=by
    unfold enclosed; rw [mem_filter]; refine ⟨And.right,fun ⟨q,hq,hp⟩=> ⟨(stages_finite _).mem_toFinset.mpr (fun i hi=>listed _ _ hq (hp hi)),_,hq,hp⟩⟩
lemma under (he:P≤Q): P.enclosed⊆Q.enclosed:=by intro p hi; obtain ⟨q,hq,h⟩:= encloses.mp hi; obtain ⟨r,hr,hh⟩:= he.2 q hq; exact encloses.mpr ⟨r,hr,h.trans hh⟩
lemma stage_in (h:p∈ P.choose): p∈P.enclosed:=encloses.mpr ⟨p,h,le_rfl⟩
lemma merge_enclosure (h:Free P Q): enclosed (merge h)=P.enclosed ∪ Q.enclosed:=by ext1 i; simp only [encloses, merge, Finset.mem_union, or_and_right, exists_or]
lemma Free.enclosed (h:Free P Q): Disjoint P.enclosed Q.enclosed:=by
    refine Finset.disjoint_left.mpr (fun i hP hQ=>?_); obtain ⟨p,hp,hP⟩:=encloses.mp hP; obtain ⟨q,hq,hQ⟩:=encloses.mp hQ; exact i.not_disjoint ((h.separate p q hp hq).mono hP hQ)
lemma under_only (p:Pod) : q∈ (only p).enclosed ↔ q≤p:= by simp only [encloses,only_mem, exists_eq_left]
-- separating ancestor guards
abbrev scars (P Q:Ensemble):= P.enclosed \ Q.enclosed
lemma scars_zip (h:P≤Q)(he:Q≤R): scars R Q ∪ scars Q P=scars R P:= by ext1 i; simp only [scars, Finset.mem_union, Finset.mem_sdiff]; have h1 : i∈ P.enclosed → i∈ Q.enclosed:= fun hi=>under h hi; have h2:i∈ Q.enclosed→ i∈ R.enclosed:= fun hi=>under he hi; tauto
lemma scars_apart (P Q R:Ensemble): Disjoint (scars R Q) (scars Q P):= Finset.disjoint_left.mpr fun i hi hh=> (mem_sdiff.mp hi).2 (mem_sdiff.mp hh).1
section
variable {A B:Ensemble}(hv:Free P Q)(he:Free A B)(hP:A≤P)(hQ:B≤Q)
include hP hQ
lemma scars_sum : scars (merge hv) (merge he)=scars P A ∪ scars Q B:=by
    unfold scars; rw [merge_enclosure,merge_enclosure]; ext1 i; simp only [Finset.mem_sdiff,Finset.mem_union]; have h1 : i∈A.enclosed→i∈P.enclosed:=fun ai=>under hP ai; have h2:i∈ B.enclosed→i∈ Q.enclosed:=fun a=>under hQ a; have h3 : i∈P.enclosed→ i∈ Q.enclosed →False:=fun hi hh=> Finset.disjoint_left.mp hv.enclosed hi hh; tauto
end
lemma scar_deny {J:Ensemble}(hp:J≤P)(hq:Q≤ P)(he:¬J≤ Q):∃ (j:J)(q r:Q)(i k:Slot), q ≠ r ∧ i∈ j.val.val ∧ i∈q.val.val ∧ k∈j.val.val∧k∈r.val.val∧assign hq q=assign hq r := by
   by_contra H; apply he; refine ⟨(ref_slots hp).trans (ref_slots hq).symm, fun j hj=> ?_⟩; let a:=j.here; let v:J:=⟨j,hj⟩; have ht:∀ i∈ j.val,i∈ Q.Along:=fun i hi=> ref_slots hq ▸ ref_slots hp ▸ listed J j hj hi -- rewrite?
   let q:=owner Q ⟨a,ht _ j.here_mem⟩; have hr : a∈ q.val.val:=belongs Q _; refine ⟨q.val,q.property,fun k hk=> ?_⟩; let r:= owner Q ⟨k,ht _ hk⟩
   have hi:k∈ r.val.val:= belongs Q _; by_contra hw; have hh : q ≠ r:=fun h=>hw (h ▸ hi)
   have hS : assign hp v=assign hq q:= serial P (inside hp v j.here_mem) (inside hq q hr)
   have hT : assign hp v=assign hq r:= serial P (inside hp v hk) (inside hq r hi); exact H ⟨v,q,r,a,k,hh,j.here_mem,hr,hk,hi,hS.symm.trans hT⟩
end YM.Frontier6.Bouquet.Ensemble
