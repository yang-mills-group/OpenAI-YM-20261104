import YM.SchemeConversionRG11.FirstMS.Triad.Vigor

/-! Total derivative for projected V. (First-order identity; no Ward assumption.) -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

variable {x:Nodes}{R ρ:ℝ}(h:Box x R ρ)(l:P→Stem)(a:Axis)

include h
lemma soft_integral (i:P){t:ℝ}(ht:0<t):Integrable (softsphere x l i a t):=
   integrates_smooth x l i a (χ:=flag x R i) (flag_smooth i) (h.flag_cost i) (h.flag_uniq i) h.confirms _ ht

omit h in
lemma bypass_bill(j:P){t:ℝ}(ht:0<t)(v:E4):
    leg x l t j v * grad a (bypass x l j t) v=∑ i∈ Finset.univ.erase j, softsphere x l i a t v:= by
   have hp : (Finset.univ.erase j).card=2:= by rw [Finset.card_erase_of_mem (Finset.mem_univ j)]; simp [P]
   obtain ⟨b,c,hb,he⟩:= Finset.card_eq_two.mp hp
   have hs (j v k:P)(hk:v∈ ({j,k}:Finset P)):=hk -- unused
   have hd (s:E4)(i:P): DifferentiableAt ℝ (leg x l t i) s:= ((leg_smooth x l i (t:=t) (v:=s) (Or.inl ht.ne')).comp (f:=fun v:E4=> (t,v)) s (by fun_prop)).differentiableAt (by simp)
   have H: ∀ i:P,i≠j ↔ i=b∨i=c:=by
      intro i
      have hD : i∈ Finset.univ.erase j ↔ i∈({b,c}:Finset P) := by rw [he]
      simpa using hD
   have hk: b≠j:= (H _).2 (Or.inl rfl); have hq:c≠j:=(H _).2 (Or.inr rfl)
   have he₁: Finset.univ.erase b={j,c}:= by
      ext w; suffices w≠b ↔ w=j∨w=c by simpa
      refine ⟨fun hx=> ?_, fun hx=> ?_⟩
      · by_cases hh:w=j; exact Or.inl hh; exact Or.inr (((H w).1 hh).resolve_left hx)
      rcases hx with hh|hh<;> subst w; exact Ne.symm hk; exact Ne.symm hb
   have he₂: Finset.univ.erase c={j,b}:= by
      ext w; suffices w≠c ↔ w=j∨w=b by simpa
      refine ⟨fun hx=> ?_, fun hx=> ?_⟩
      · by_cases hh:w=j; exact Or.inl hh; exact Or.inr (((H w).1 hh).resolve_right hx)
      rcases hx with hh|hh<;> subst w; exact Ne.symm hq; exact hb
   have hh : bypass x l j t= fun v=> leg x l t b v*leg x l t c v:= by funext u; unfold bypass; rw [he,Finset.prod_pair hb]
   rw [hh,he,Finset.sum_pair hb]; unfold softsphere; rw [←leg_gradient,←leg_gradient]; unfold bypass grad D; rw [he₁,he₂, Finset.prod_pair (Ne.symm hq), Finset.prod_pair (Ne.symm hk), fderiv_fun_mul (hd _ _) (hd _ _)]; simp; ring

lemma charge_erases (hl:∀ i,(l i).loc=i): (∑ j:P, multiplies l j a x R ρ 0)=0:= by
   apply tendsto_nhds_unique_of_eventuallyEq (tendsto_finsetSum (Finset.univ (α:=P)) (fun j _=> result h l j a hl h.confirms)) tendsto_const_nhds
   filter_upwards [self_mem_nhdsWithin] with t ht
   have hp:0<t:=ht
   let f(i:P):= leg x l t i
   have hU(i:P):= soft_integral h l a i hp
   let T (v:E4):= ∑ i∈Finset.univ.erase (0:P), softsphere x l i a t v
   let B:= bypass x l 0 t
   have H : T = fun v=> f 0 v*grad a B v := funext fun v=> (bypass_bill (x:=x) l a 0 hp v).symm
   have hi : Integrable T:= integrable_finsetSum _ fun i _=> hU i
   have hd : Integrable (fun v=> surface x l 0 a t v *B v):= hU 0
   let I := fun i=> ∫ v,softsphere x l i a t v
   have hx : I 0+(∑ i∈Finset.univ.erase (0:P),I i)=0 := by
      have hg : Integrable (fun v=> f 0 v *grad a B v):= H ▸ hi
      have hh : I 0 = ∫ v, grad a (f 0) v*B v:= by unfold I; simp_rw [f,leg_gradient]; rfl
      have he : (∫ v, f 0 v*grad a B v)=-(∫ v,grad a (f 0) v* B v) := by
         have hf : Differentiable ℝ (f 0):= fun v=> ((leg_smooth x l 0 (t:=t) (v:=v) (Or.inl hp.ne')).comp (f:=fun v:E4=> (t,v)) v (by fun_prop)).differentiableAt (by simp)
         have hs : Differentiable ℝ B:= fun v=> ((bypass_smooth x l 0 (t:=t) (v:=v) (fun i _=>Or.inl hp.ne')).comp (f:=fun v:E4=>(t,v)) v (by fun_prop)).differentiableAt (by simp)
         have ht' : Integrable (fun v=> grad a (f 0) v * B v):= by simp_rw [f,leg_gradient]; exact hd
         exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ht' hg (stem_earnest x l 0 h.confirms hp) (fun v _=> hf v) (fun v _=> hs v)
      rw [hh, show (∑ i∈Finset.univ.erase (0:P),I i)=(∫ v,T v) from (integral_finsetSum _ (fun i _=> hU i)).symm, H, he]; ring
   change ∑ j:P,(I j:ℂ)=0
   rw [←ofReal_sum, ← Finset.add_sum_erase _ I (Finset.mem_univ 0),hx,ofReal_zero]

-- topological tensor (ordered). delta = coef(e−)*... - coef(e+)*...
def tension (w:Bool)(a b c d:Axis) :ℤ:= ∑ i:Fin 3,fanI w i a b*fanI w i c d
def skew(a b c d:Axis):ℤ:= tension false a b c d - tension true a b c d
omit h
section Integer
set_option maxRecDepth 25000
set_option maxHeartbeats 800000
attribute [-instance] Classical.propDecidable
lemma turns : ∀ a b c d:Axis,skew a b c d=skew a d b c := by decide
lemma complete : ∀ a b c d:Axis,
    tension false a b c d + tension true a b c d = 2* ((if a=c ∧ b=d then 1 else 0)-(if a=d ∧ b=c then 1 else 0)):=by decide
end Integer
lemma valve (w:Bool)(a b c d:Axis) : (∑ i:Fin 3,(fan w i a b:ℂ)*fan w i c d)= 2⁻¹ * (tension w a b c d:ℂ):=by
   unfold tension fan; simp_rw [Int.cast_sum,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> ?_
   push_cast
   rw [div_mul_div_comm,← ofReal_mul,sqrt_two_rule, ofReal_ofNat]; ring

end YM.SchemeConversionRG11.FirstMS.Triad
