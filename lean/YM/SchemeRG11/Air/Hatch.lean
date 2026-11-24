import YM.SchemeRG11.Long.Rim
/-! Extension of difference Taylor bounds on coordinate patches.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Air
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open Labels Long
open scoped Classical Pointwise
variable {G:Gauge} {n:ℕ} {T:Align.Itinerary} {R r:ℝ}
def flight (p:Cover):ℕ:=∑ i: Axis,(p i).natAbs -- ambiguity
lemma rail (p:Cover): (Air.flight p:ℝ)≤4*World.d p:=by
 unfold Air.flight World.d; have he: (∑ i:Axis,(p i).natAbs) ≤ ∑ _:Axis,Catch.diam p:= Finset.sum_le_sum (fun i _=>diam_ge ..); simp only [Finset.sum_const,Finset.card_univ,Axis,Fintype.card_fin,nsmul_eq_mul] at he
 apply (Nat.cast_le (α:=ℝ)).mpr he|>.trans; push_cast; linarith
lemma footing {x:Cover}(he:x≠0) :∃ y: Cover,∃i:Axis, (x=y+step i ∨ y=x+step i) ∧ (∀j:Axis,(y j).natAbs ≤ (x j).natAbs) ∧ Air.flight y+1=Air.flight x:=by
 obtain ⟨i,hi⟩:= Function.ne_iff.mp he; change x i≠0 at hi
 have H(p: Cover)(h:(p i).natAbs+1=(x i).natAbs)(u:∀j:Axis,j≠i→p j=x j): (∀j,(p j).natAbs ≤(x j).natAbs)∧Air.flight p+1=Air.flight x:=by
    refine ⟨fun j=>?_,?_⟩
    · rcases eq_or_ne j i with a|a; · subst j; omega
      rw [u j a]
    unfold Air.flight; rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),← Finset.sum_erase_add Finset.univ (Finset.mem_univ i) (f:=fun j=>(x j).natAbs)
           ]; rw [add_assoc,h]; congr 1; exact Finset.sum_congr rfl (fun j hj=>by rw [u j (Finset.mem_erase.mp hj).1])
 rcases lt_or_gt_of_ne hi with H'|H'
 · refine ⟨x+step i,i,Or.inr rfl,H _ ?_ ?_⟩; · simp only [Pi.add_apply,step_apply, ↓reduceIte]; omega
   intro j hj;simp [hj]
 refine ⟨x-step i,i, Or.inl (by rw [sub_add_cancel]),H _ ?_ ?_⟩; · simp only [Pi.sub_apply,step_apply, ↓reduceIte]; omega
 intro j hj; simp [hj]
lemma dial {S:ℝ}{B L:ℝ}{u v:ℤ}(h:v≥0)(ht:B≥0)(hp:L≥0) (f:Plane ℝ)(i:ℕ) (hv:|f 0|≤ B*T.gap i^u)(hx:∀j:Axis,∀p,Near T S i p→ |soar j f p|≤L*T.gap i^u*World.d p^v)(z:Cover)(hz:Near T S i z): |f z| ≤ (B+4*L)*T.gap i^u*World.d z^(v+1):=by
 have w(y:Cover)(he:Near T S i y): |f y| ≤ B*T.gap i^u +(Air.flight y:ℝ)*L*T.gap i^u*World.d y^v:=by
   induction H:Air.flight y using Nat.strong_induction_on generalizing y with | h k ih=>
   rw [← H]; by_cases q:y=0
   · subst y; simpa only [Air.flight,Pi.zero_apply,Int.natAbs_zero,Finset.sum_const_zero,Nat.cast_zero,zero_mul,add_zero] using hv
   obtain ⟨p,j,g,V,Q⟩:=footing q
   have hb : World.d p≤ World.d y:=by
      have ht: Catch.diam p≤Catch.diam y:=Finset.sup_le (fun i _=> (V i).trans (diam_ge y i)); unfold World.d; gcongr
   have hv:Near T S i p:= (mul_le_mul_of_nonneg_left hb (T.positive _).le).trans he
   have hk:= ih _ (show Air.flight p<_ by omega) _ hv rfl -- check
   have hh:L*T.gap i^u*World.d p^v≤ L*T.gap i^u*World.d y^v:= mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ h (World.d_pos p).le hb) (mul_nonneg hp (zpow_pos (T.positive _) _).le)
   have hu:|f y|≤|f p|+L*T.gap i^u*World.d y^v:=by
      rcases g with H|H
      · rw [show f y= f p+soar j f p by nth_rw 1 [H]; apply ascend]; exact (abs_add_le ..).trans (add_le_add_right ((hx j p hv).trans hh) _)
      have hh:f y=f p-soar j f y:=by rw [H,soar_apply]; abel
      rw [hh]; exact (abs_sub ..).trans (add_le_add_right (hx j y he) _)
   apply hu.trans
   apply (add_le_add_left hk _).trans; rw [← Q]; push_cast; have he:=mul_le_mul_of_nonneg_left hh (show (Air.flight p:ℝ)≥0 by positivity); linarith only [he]
 apply le_trans (w z hz); rw [add_mul,mul_comm 4 L,add_mul]; refine add_le_add ?_ ?_
 · apply le_mul_of_one_le_right (mul_nonneg ht (zpow_pos (T.positive _) _).le) (one_le_zpow₀ (World.d_le z) (by omega))
 have hi := mul_le_mul_of_nonneg_right (rail z) (mul_nonneg (mul_nonneg hp (zpow_pos (T.positive i) u).le) (zpow_pos (World.d_pos z) v).le)
 rw [zpow_add₀ (World.d_pos z).ne', zpow_one]; linarith only [hi]
end YM.SchemeRG11.Air
