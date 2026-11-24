import YM.MSbar.Domain.Account

/-! double trace of pairs. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Domain
open Dim Symbol Super Loops MeasureTheory Function Set Filter
open scoped Topology BigOperators Classical ContDiff
variable {T C:Type} [AddCommGroup T] [Module ℝ T] {m n j:ℕ} {U:Set ℂ} {X:ℕ→Type}{S:Site X} {p q:Prop}
lemma two_sum {f : C→T→ℂ}(I:Finset C) (h:∀ i∈I, Two p (f i)) : Two p (fun x=>∑ i∈I,f i x) := by simp_rw [← Finset.sum_apply]; exact Two.sum h
lemma one_sum {f : C→T→ℂ}(I:Finset C) (h:∀ i∈I, Dim.One p (f i)) : Dim.One p (fun x=>∑ i∈I,f i x) := by simp_rw [← Finset.sum_apply]; exact Dim.One.sum h
lemma two_stage (F:∀m,X m × Hat m→ℂ)(s:ℂ)(W:Motion X)(x:T→X m) (he:∀ y,Two p (fun t:T=> F m (x t,y))) (hh:∀ y,Two p (fun t:T=>F (m+1) (above W (x t),y))) : Two p (fun t:T=> metric W q s F m (x t)) := by
    unfold metric; let V(t:T):= ∑ y∈ index q m,F m (x t,y); have hv:Two p V:= two_sum _ fun i _=> he i
    split_ifs; exact hv.add ((hh _).scale (2*(s-m):ℂ)); simpa using hv -- method arg order?
lemma one_stage (F:∀m,X m × Hat m→ℂ)(s:ℂ)(W:Motion X)(x:T→X m)(he:∀ y,Dim.One p (fun t:T=> F m (x t,y)))(hh:∀ y,Dim.One p (fun t:T=> F (m+1) (above W (x t),y))) : Dim.One p (fun t:T=> metric W q s F m (x t)) := by
    unfold metric; let V(t:T):= ∑ y∈ index q m,F m (x t,y); have hv:Dim.One p V:= one_sum _ fun i _=> he i
    split_ifs; exact hv.add ((hh _).scale (2*(s-m):ℂ)); simpa using hv
lemma stage_vanish (F:∀m,X m × Hat m→ℂ)(s:ℂ)(W:Motion X)(x:X m) (he:∀ y,F m (x,y)=0)(hh:∀ y,F (m+1) (above W x,y)=0): metric W p s F m x=0:=by simp [metric,he,hh]
abbrev Device (X:ℕ→Type) (m:ℕ) := (X m × Hat m) × Hat m
def duplex (S: Motion X)(p q:Prop)(z:ℂ)(F:∀m,Device X m→ℂ):= metric S p z (metric (S.prod vectors) q z F)
lemma discrete (S: Motion X)(F:∀m,Device X m→ℂ)(x:X m): duplex S p q m F m x= ∑ v∈ index p m,∑ w∈ index q m,F m ((x,v),w):=by simp only [duplex,Trace.sampling]
lemma duplex_zero {F:∀m,Device X m→ℂ} (S:Motion X)(x:X m)(z:ℂ)(h:∀ i:ℕ,∀ V:Move m i,∀ v w,F i ((S.move V x,v),w)=0): duplex S p q z F m x=0:=by
    unfold duplex; refine stage_vanish _ _ _ _ (fun v=> stage_vanish _ _ _ _ (fun w=>?_) (fun w=> h _ (up m) ..)) (fun v=> stage_vanish _ _ _ _ (fun w=>h _ (up m) ..) (fun w=> ?_))
    · rw [← S.triv x]; -- `triv` rewrites? then apply
      exact h _ LinearIsometry.id ..
    change F _ ((above S (above S x),_),w)=_; unfold above; rw [← S.together]; exact h _ _ ..
lemma duplex_cost {F: Record (Device X)} (p q:Prop) (h : Eligible U j ((S.prod Site.moving).prod Site.moving) F) (hp:∀ z∈U,∀ m x w,Two p fun v=> F z m ((x,v),w))(hq:∀ z∈U,∀ m x v,Two q fun w=> F z m ((x,v),w)) : Eligible U j S (fun z=> duplex S.toMotion p q z (F z)):=by
    have hv:=h.trace q (fun z hz i a=>hq z hz i a.1 a.2)
    refine hv.trace p ?_
    intro z hz n x; refine two_stage (F z) z _ (fun v: Hat n=>(x,v)) (fun w=>hp z hz n x w) (fun w=>?_); exact (hp z hz _ (above S.toMotion x) w).compose (up n).toLinearMap

-- linearity of metrics, PU
lemma metric_add {F G:∀m,X m × Hat m→ℂ} (S:Motion X) (z:ℂ) (p:Prop) : metric S p z (F+G)=metric S p z F+metric S p z G:=by
   funext i x; simp only [metric,Pi.add_apply,Finset.sum_add_distrib]; split_ifs <;> ring
lemma metric_scale {F:∀m,X m × Hat m→ℂ} (S:Motion X) (z c:ℂ)(p:Prop): metric S p z (c•F)=c • metric S p z F:=by
   funext i x; simp only [metric,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]; split_ifs <;> ring
lemma trSum (I:Finset C)(F:C → ∀m,X m × Hat m→ℂ)(S:Motion X)(z:ℂ): metric S p z (∑ i∈I,F i)=∑ i∈I,metric S p z (F i):=by induction I using Finset.induction_on with | empty=> rw [Finset.sum_empty,Finset.sum_empty]; funext x h; simp [metric] | insert i I ht ih=> rw [Finset.sum_insert ht,Finset.sum_insert ht,metric_add,ih]
lemma dux_add {F G:∀m,Device X m→ℂ}(S: Motion X)(z:ℂ) : duplex S p q z (F+G)=duplex S p q z F+duplex S p q z G:=by unfold duplex; rw [metric_add, metric_add]
lemma dux_scale {F:∀m,Device X m→ℂ}(S:Motion X)(z c:ℂ) : duplex S p q z (c•F)=c • duplex S p q z F:=by unfold duplex; rw [metric_scale,metric_scale]
end YM.MSbar.Domain
