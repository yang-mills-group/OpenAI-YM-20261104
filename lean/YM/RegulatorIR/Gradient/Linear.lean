import YM.RegulatorIR.Gradient.Line

/-! Identify the linear pieces of the exact transformation, even on localized
(not necessarily finite-grid) packets. No gauge assumption is needed on the
input for the combinatorics. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Gradient
open Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Train Uniform Diagram Function Finset
open scoped ENNReal Topology BigOperators Classical
variable {X Y Z : Type}{r:ℕ}
section Ray
variable (T:Packet X r)(K:Layer X X)(x v:Tuple X r)(s:List (Fin r))

def covers (v x:Tuple X r) (s:List (Fin r)):Prop:=∀ i, i∉s → x i=v i
def field (T:Packet X r)(K:Layer X X)(x:Tuple X r)(s:List (Fin r))(v:Tuple X r):ℝ:= if covers v x s then T v * ∏ i∈s.toFinset, K (x i) (v i) else 0

lemma field_cost {c:ℝ≥0∞}(H:height K c)(v):‖field T K x s v‖ₑ ≤ ‖T v‖ₑ * c^s.toFinset.card:=by
 unfold field; split
 · rw [enorm_mul]; apply mul_le_mul_right
   generalize s.toFinset=w
   induction w using Finset.induction_on with
   | empty=> simp
   | insert i s h ih=>
       rw [Finset.prod_insert h,Finset.card_insert_of_notMem h, pow_succ,enorm_mul]
       exact (mul_le_mul' (H ..) ih).trans_eq (mul_comm ..)
 rw [enorm_zero]; exact bot_le
lemma field_sum {c:ℝ≥0∞}(H:height K c)(hc:c≠⊤)(h:quota T 1≠⊤): Summable (field T K x s):= by
 apply quota_summable (w:=1) (fun _=>le_rfl)
 apply ne_top_of_le_ne_top (ENNReal.mul_ne_top h (show c^s.toFinset.card ≠ ⊤ from by finiteness)); rw [quota_base,quota_base, ← ENNReal.tsum_mul_right]; exact ENNReal.tsum_le_tsum (field_cost T K x s H)

lemma ray_assembly {c:ℝ≥0∞}(H:height K c)(h:quota T 1≠⊤)(hc:c≠⊤)(hz:s.Nodup): drawing T K s x=∑' i,field T K x s i:=by
 induction s generalizing x with
 | nil=>
   unfold drawing; rw [tsum_eq_single x]
   · simp [field,covers]
   intro z hv; apply if_neg
   intro h; exact hv (funext fun i=> (h i (by simp)).symm)
 | cons a s ih=>
   rw [← Stalk.collected_sum (fun i:Tuple X r=>i a) (field_sum T K x (a::s) H hc h),drawing]; unfold ray; apply tsum_congr;intro y
   let g (p:Tuple X r):=p a
   let Z:=update x a y
   let X:=field T K Z s
   unfold swivel; rw [ih _ (List.nodup_cons.mp hz).2]
   have ha:a∉s:= (List.nodup_cons.mp hz).1
   have hK:X= (g ⁻¹' {y}).indicator X:=by
      ext i; by_cases ht:g i=y
      · rw [Set.indicator_of_mem (by simpa using ht)]
      rw [Set.indicator_of_notMem (by simpa using ht)]
      apply if_neg; intro H;apply ht
      exact (H a ha).symm.trans (Function.update_self ..)
   have hv:(∑' v,X v) = ∑' i:Stalk g y,X i.val:=by calc
      _ = ∑' x, ((g ⁻¹' {y}).indicator X) x:= tsum_congr fun x=>congr_fun hK x
      _ = _:= (_root_.tsum_subtype _ X).symm
   rw [hv,← tsum_mul_left]; apply tsum_congr; intro ⟨v,hv⟩
   change K _ _ * (field _ _ Z _ v)=field _ _ _ (a::s) v
   change v a=y at hv
   have hE : covers v Z s↔covers v x (a::s):=by
      constructor
      · intro h i hi
        have hp:=h i (fun hx=>hi (List.mem_cons_of_mem a hx));rw [show Z i=x i from Function.update_of_ne (fun he=>hi (by rw [he];simp)) ..] at hp; exact hp
      intro h i hi; by_cases he:i=a
      · subst i; exact (Function.update_self ..).trans hv.symm
      rw [show Z i=x i from Function.update_of_ne he ..]
      exact h i (by simp [hi,he])
   unfold field
   rw [List.toFinset_cons,prod_insert (by simpa using ha)]
   by_cases hp:covers v Z s
   · rw [if_pos hp,if_pos (hE.mp hp),hv]
     have he : ∏ i∈s.toFinset,K (Z i) (v i)=∏ i∈s.toFinset,K (x i) (v i) := prod_congr rfl (fun i hi=> congr_arg (fun y=> K y (v i)) (Function.update_of_ne (fun h=>ha (by simpa [h] using hi)) ..))
     rw [he]; ring
   rw [if_neg hp, if_neg (fun he=> hp (hE.mpr he)),mul_zero]
lemma ray_full {c:ℝ≥0∞}(H:height K c)(h:quota T 1≠⊤)(hc:c≠⊤):
    drawing T K (List.finRange r) x = ∑' t:Tuple X r, T t * ∏ i,K (x i) (t i) := by
 rw [ray_assembly _ _ _ _ H h hc (List.nodup_finRange r)]; simp [field,covers]
end Ray
end YM.RegulatorIR.Gradient
