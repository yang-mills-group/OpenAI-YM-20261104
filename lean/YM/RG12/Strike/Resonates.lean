import YM.RG12.Strike.Wake
/-! # Kiln. Only critical toll amounts matter for the complete first-order anomaly
 on the integrated two-mark coefficient. `Waive` gives EXACT power law on continuous scale
 interval after engineering. No log component even at infinitesimal generator. Prices of coefficients
 held only at each separated point (profile smearing entails further control; arrays at positive point here).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable (χ:R→ℂ)(F G:R→ℂ)(a b:ℕ) (z:R)
-- necessary denominator costs not assumed. pointwise statement.
-- give generous exponent grade H; sum over positive powers ONLY.
def Waive (H:ℕ)(F:ℝ→ℂ):Prop:=∃ c:Fin H→ℂ,∀ t:ℝ,0<t→ F t = ∑ i:Fin H,c i * ((t:ℂ)^(i.val+1)-1)
variable {H:ℕ}{f g:ℝ→ℂ}
lemma Waive.congr (ha:Waive H f) (h:∀ i:ℝ,0 < i→f i=g i): Waive H g:=by obtain ⟨c,he⟩:=ha; exact ⟨c,fun t ht=> (h t ht).symm.trans (he t ht)⟩
lemma Waive.nada (H:ℕ): Waive H 0:=by use 0;simp
lemma Waive.merge (hf:Waive H f)(hg:Waive H g): Waive H (f+g):=by
  obtain ⟨a,he⟩:=hf;obtain ⟨b,hu⟩:=hg; refine ⟨a+b,fun t ht=>?_⟩
  simp only [Pi.add_apply,he t ht,hu t ht,add_mul,Finset.sum_add_distrib]
lemma Waive.sent {ι:Type*}{s:Finset ι}{F:ι→ℝ→ℂ}(hF:∀ i∈s,Waive H (F i)):Waive H (fun t=>∑ i∈s,F i t):=by
    induction s using Finset.cons_induction_on with
    | empty=>simp only [Finset.sum_empty]; exact Waive.nada _
    | cons a s he ih=>
       simp only [Finset.sum_cons]; exact Waive.merge (hF a (by simp)) (ih (fun i hi=> hF _ (by simp [hi])))
lemma Waive.credit (hf:Waive H f)(a:ℂ):Waive H (fun x:ℝ=>a*f x) :=by
   obtain ⟨c,hc⟩:=hf; refine ⟨fun i=>a*c i,?_⟩;intros; simp only [hc _ (by assumption),Finset.mul_sum,mul_assoc]
lemma Waive.monomial (c:ℂ)(p:ℕ)(hp:p≤H): Waive H (fun t=>c*((t:ℂ)^p-1)):=by
   rcases p with -|p
   · simp only [pow_zero,sub_self,mul_zero]; exact Waive.nada _
   let i:Fin H:= ⟨p,hp⟩
   use Pi.single i c
   intro t _; rw [Finset.sum_eq_single i]; simp [i]
   · intro b _ h; rw [Pi.single_eq_of_ne h,zero_mul] -- zero_mul actually
   simp
-- also monotone H by character transform.
lemma Waive.upper (hf:Waive H f){m:ℕ}(h:H≤m):Waive m f:=by
   obtain ⟨c,hc⟩:=hf
   exact (Waive.sent (s:=Finset.univ) (fun (i:Fin H) _=> Waive.monomial (H:=m) (c i) (i.val+1) (by have hi:=i.isLt;omega))).congr fun i hi=> (hc i hi).symm
-- separate each mark from oar criterion (only highest moment of each can resonate). coefficient budget a+b-4.
def easter (χ F G:R→ℂ)(a:ℕ)(x:R)(t:ℝ):=∑ n∈Finset.range (a-3),toll χ (layer F G x n) t
-- highest possible anomalous toll. asks actual sum when incorporating i-j contractions
-- k=3 case separately. general Nat a,b allowed.
def crit (χ F G:R→ℂ)(a:ℕ)(x:R)(t:ℝ):ℂ:=if 4 ≤ a then toll χ (layer F G x (a-4)) t else 0
variable {χ F G a b}(hχ:Base χ)(hf:Garden F a)(hg:Garden G b)
include hχ hf hg
omit hg in
lemma kiln (ha:3≤a)(hb:3≤b): Waive (a+b-4) (easter χ F G a z - crit χ F G a z):=by
  unfold easter crit
  by_cases h:4≤a
  · have he : (a-3)=a-4+1:=by omega
    simp only [h,ite_true,he,sum_range_succ]; set H:=a+b-4
    let v(n:ℕ):=toll χ (layer F G z n)
    change Waive H ((fun t=>(∑ n∈Finset.range (a-4),v n t)+v (a-4) t) - fun t=> v (a-4) t)
    apply (Waive.sent (F:=v) (s:=Finset.range (a-4)) ?_).congr
    · intro i _; exact (add_sub_cancel_right ..).symm
    intro i hi
    have hi:=Finset.mem_range.mp hi
    obtain ⟨C,hC⟩:=money (f:=F) (g:=G) i (a-4-i) hχ hf (by omega : a=4+i+(a-4-i)) z (by omega : 0<a-4-i)
    exact (Waive.monomial C (a-4-i) (by unfold H; omega : a-4-i ≤ H)).congr (fun t ht=> (hC t ht).symm)
  have he:a=3:=by omega
  simp only [show a=3 from he] at *
  change Waive _ ((fun t=>(∑ n∈Finset.range 0,_))- fun t=>if 4 ≤ 3 then _ else _)
  simp only [show ¬4 ≤ (3:ℕ) by decide,if_false, Finset.range_zero,Finset.sum_empty,sub_self]; exact Waive.nada _
-- peel both, only ask summed critical reading
variable {ι:Type*}{s:Finset ι}{A B:ι→R→ℂ}(hA:∀ i∈s,Garden (A i) a)(hB:∀ i∈s,Garden (B i) b)
omit hf hg
include hA hB
def Gap (x:R)(H:ℕ)(f:R→ℂ)(t:ℝ):ℂ:=f x-(t:ℂ)^H*f (t•x)
-- linear!
lemma pile (ha:3≤a)(hb:3≤b)(hz:z≠0)
    (h:∀ t:ℝ,0<t→∑ i∈s,crit χ (A i) (B i) a (-z) t=0)
    (h':∀ t:ℝ,0<t→∑ i∈s,crit χ (B i) (A i) b z t=0):
 Waive (a+b-4) (Gap z (a+b-4) (fun x=>∑ i∈s,frosted χ (A i) (B i) a b x)):=by
   let X:=a+b-4
   apply (Waive.merge (Waive.sent (s:=s) (fun i hi=> kiln (-z) hχ (hA i hi) (G:=B i) ha hb)) (Waive.sent (s:=s) (fun i hi=>show Waive X (easter χ (B i) (A i) b z - crit χ (B i) (A i) b z) from (by simpa only [X,Nat.add_comm b a] using! kiln (G:=A i) z hχ (hB i hi) hb ha)))).congr
   intro t ht; unfold Gap
   simp only [Pi.add_apply,Pi.sub_apply,sum_sub_distrib,h t ht,h' t ht,sub_zero]; rw [←Finset.sum_add_distrib]; simp only [easter,Finset.mul_sum,←Finset.sum_sub_distrib]
   exact Finset.sum_congr rfl (fun i hi=> (oar hχ (hA i hi) (hB i hi) t hz ht ha hb).symm)
end YM.RG12.Strike
