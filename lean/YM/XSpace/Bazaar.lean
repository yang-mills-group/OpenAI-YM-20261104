import YM.XSpace.Rail

/-!
# Multi-source composition and startup permit algebra

Use unnormalized scalar Wick after composing normalized open fields with literal freeze.
Permit knows NOTHING of gauge or positions; appointments arrive independently.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stall
open Function Filter Set Lattice Mu Trace MvPolynomial Next.Rank.Normal Contraction Chart2 JetGauge Future Drama
open scoped Topology BigOperators
variable {ι Y I:Type} {L: Filter ι} {G:Gauge}
variable (N:Accepts ι Y)

def Permit (L:Filter ι)(N:Accepts ι Y):Prop:=∀ p∈N,∀ c:ι→ℂ, Likely L c→(fun i y=> c i*p i y) ∈N
structure Shops (a:ι→ℝ)(L:Filter ι)(H:Club G ι)(F:I→ι→Cover)(s:Finset I) : Prop where
  pairs : ∀ j∈s,∀ r∈s,j≠r→∀ q p:Fee G,Stops q.line→Stops p.line → Likely L fun i=> (↑(handshake (Calling (F j) a q i) (Calling (F r) a p i)):ℂ)
  births : ∀ i∈s,∀ q:Fee G,Stops q.line→(fun j:ι=> bake (Calling (F i) a q j))∈H

def web (s:Finset I)(v:I→ι→Stamp G)(j:ι):= ∏ i∈s,freeze (v i j)
def starOrder (s:Finset I)(v:I→ Stamp G):Stamp G:=flicker (∏ i∈s,freeze (v i))
def hall (s:Finset I)(v:I→ι→Stamp G)(Q:ι→Y→ Stamp G)(j:ι)(y:Y):= E (root G) (freeze (Q j y)*web s v j)
private def pending (s:Finset I)(v:I→ι→Stamp G)(g:ι→Stamp G)(P:ι→Y→ Stamp G)(j:ι)(y:Y):ℂ:= E (root G) (freeze (P j y)*(freeze (g j)*web s v j))
lemma accepts_one (A:Stamp G)(L:Line G) : E (root G) (harp L*A)= E (root G) (D (bake L) A):=by
  conv=> lhs; arg 2; rw [← came (harp L*A)]; skip
  conv=> rhs; arg 2; rw [← came (D _ A)]; skip
  rw [← counts,← counts,ripple,map_add, map_mul,scalar,leg_test,map_zero, Complex.ofReal_zero,zero_mul,zero_add]; rfl
private lemma bore (P Q W:Stamp G)(L:Line G): E (root G) (freeze P * (freeze (harp L*Q) * W))= E (root G) (freeze (D (bake L) P) * (freeze Q*W))+E (root G) (freeze P*(freeze Q*(D (bake L) W))):=by
  let g:=D (bake L); rw [winter,sub_mul,mul_sub,map_sub]; rw [show freeze P*(harp L*freeze Q*W)=harp L*(freeze P*(freeze Q*W)) by ring, accepts_one]; rw [(D _).leibniz,(D _).leibniz, slip, sub_eq_iff_eq_add]; simp only [smul_eq_mul, mul_add,map_add]; ring_nf; rw [show part (G:=G) _ (freeze Q)=D (bake L) (freeze Q) from rfl]; abel
variable {F:I→ι→Cover}{a:ι→ℝ}{s:Finset I} {k:ℕ} {H:Club G ι}
section
variable [DecidableEq I]
lemma replace (s:Finset I)(v:I→ι→Stamp G)(g:ι→Stamp G)(i:I)(hi:i∉s)(j:ι):web s (update v i g) j=web s v j:=by unfold web; exact Finset.prod_congr rfl fun k hk=> by rw [update_of_ne (by rintro rfl; contradiction)]
lemma webpage (s:Finset I)(v:I→ι→Stamp G)(g:ι→Stamp G)(i:I)(hi:i∉s)(P:ι→Y→Stamp G): hall (insert i s) (update v i g) P = pending s v g P:=by funext x y; unfold hall pending web; rw [Finset.prod_insert hi, update_self,show ∏ j∈s,freeze (update v i g j x)= _ from replace s v g i hi x];rfl
private lemma derivative (s:Finset I)(v:I→ι→Stamp G)(B:ι→ Contact G)(j:ι):D (B j) (web s v j)=∑ i∈s,web s (update v i (Records.strike B (v i))) j:=by
  induction s using Finset.induction_on with
  | empty=> simp [web]
  | insert i s hi ih=> have he (p:I→ι→Stamp G): web (insert i s) p j=freeze (p i j)*web s p j:= Finset.prod_insert hi; rw [he,(D _).leibniz, Finset.sum_insert hi,ih,he,update_self,replace _ _ _ _ hi]; change _=freeze _* _ + _; rw [show freeze (Records.strike _ _ j)=_ from slip ..]; simp only [smul_eq_mul, Finset.mul_sum]; rw [add_comm,mul_comm (web ..)]; congr 1; exact Finset.sum_congr rfl fun k hk=> by rw [he,update_of_ne (by rintro rfl; contradiction)]

-- IH on all other sources. Proves ascent by adding any multiplicative leg, carrying lower operator slots of exactly the unchanged weights on other prices.
lemma pays (s:Finset I)(Z:Shops a L H F s)(J:Permit L N)(v:I→ι→Stamp G)(ht:∀ i∈s, Records a L (F i) (v i))(Q:ι→Y→Stamp G)(h:Admits N H Q): hall s v Q∈ N:=by
  induction s using Finset.induction_on generalizing Q v with
  | empty=>
    have he: hall ∅ v Q=fun i y=> scalar G (Q i y):= funext fun i=>funext fun y=> by rw [hall, web, Finset.prod_empty, mul_one,counts]
    rw [he]; exact h.2 0 (Submodule.zero_mem _)
  | insert i s hi ih=>
    have hN:Shops a L H F s:=⟨fun i hi j hj=> Z.pairs i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj),fun j hj=> Z.births j (Finset.mem_insert_of_mem hj)⟩
    have node (g:ι→Stamp G) (hh:Records a L (F i) g): ∀ x:I→ι→Stamp G,(∀ j∈s,Records a L (F j) (x j))→∀ Q:ι→Y→Stamp G,Admits N H Q→ pending s x g Q∈ N:= by
      induction hh with
      | zero=> intro x hx Q h; unfold pending; simp_rw [Pi.zero_apply,map_zero,zero_mul,mul_zero]; exact Submodule.zero_mem _
      | unit=>
        intro x hx Q h; have he: pending s x 1 Q= hall s x Q:=funext fun i=> funext fun j=>by simp [pending,hall]
        rw [he]; exact ih hN x hx Q h
      | @scale A h₁ b hb IH=>
        intro x hx Q h; have he: pending s x (chain b A) Q=fun i y=> b i • pending s x A Q i y:= funext fun i=> funext fun y=>by simp [pending,chain,mul_smul_comm,smul_mul_assoc]
        rw [he]; exact J _ (IH x hx Q h) _ hb
      | @add A B h₁ h₂ i j=>
        intro x hx Q h; have he:pending s x (A+B) Q = pending s x A Q + pending s x B Q:= by funext i y; simp [pending,mul_add,add_mul]
        rw [he]; exact Submodule.add_mem _ (i x hx Q h) (j x hx Q h)
      | @receive p h₁ B hB IH=>
        intro x hx Q h; set R:= Calling (F i) a p; let D t:= bake (R t); have he: pending s x (pencil R*B) Q= pending s x B (fun j k=> part (D j) (Q j k))+∑ u∈s,pending s (update x u (Records.strike D (x u))) B Q:=by
          funext j y; unfold pending; rw [Pi.mul_apply,pencil, bore, derivative s x D j]; simp only [Finset.sum_apply,Pi.add_apply,Finset.mul_sum,map_sum];rfl
        rw [he]; refine Submodule.add_mem _ (IH x hx _ (admit_steps N H h (Z.births i (by simp) p h₁))) (Submodule.sum_mem _ fun j hj=> IH _ ?_ Q h)
        intro k hk; by_cases h:k=j; subst k; rw [update_self]; apply Records.biting (hx _ hj) (fun y he=>Z.pairs i (by simp) j (Finset.mem_insert_of_mem hj) (by rintro rfl; contradiction) p y h₁ he)
        rw [update_of_ne h]; exact hx k hk
    rw [show hall (insert i s) v Q=pending s v (v i) Q from ?_]; exact node _ (ht i (by simp)) v (fun j hj=> ht j (by simp [hj])) _ h
    conv=> lhs; rw [show v=update v i (v i) from (update_eq_self ..).symm]; skip
    rw [webpage _ _ _ _ hi]
end
end YM.XSpace.Stall
