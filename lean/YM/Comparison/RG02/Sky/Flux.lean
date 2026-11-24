import YM.Comparison.RG02.Sky.Nets
import YM.SectorNext.RECONNECTED_LOCALITY.Optional
import YM.Push.ABSOLUTE_SUMS.Basic
/-!
# Anchored marginal values for cover instructions

 Use fiber sums with absolute summability. `push` convention supplies genuine charged estimates
 before any identification of position data. One indicated root -- if supplies depend on that
 choice, keep orientation in billing the whole output. Sparse sector implementation can apply
 masks only when proved (no faith in pointwise equality of two charged exponents).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Sky.Flux
open Function Filter Finset RG Push.AbsoluteSums
open SectorNext.Reconnect.Optional
open scoped Classical Topology BigOperators
variable {E A B C D : Type*} [NormedAddCommGroup E] [CompleteSpace E]
   (p:A→B)

def push (f : A→ E) (x:B): E:= ∑' i : p ⁻¹' {x}, f i.val -- subtypes {a|p a=x}
omit [CompleteSpace E] in
lemma push_if [DecidableEq B] (f:A→E) (x:B) : push p f x=∑' i:A,(if p i=x then f i else 0):= by
   rw [push,_root_.tsum_subtype]; refine tsum_congr fun i=>?_ ; by_cases h:p i=x <;> simp [h]
lemma push_sum (f:A→E)(h:Summable f) : Summable (push p f) := (h.hasSum.tsum_fiberwise p).summable -- subtype
lemma push_all {f:A→E}(h:Summable f) : (∑' x,push p f x)=∑' i,f i:= (h.hasSum.tsum_fiberwise p).tsum_eq
lemma support (f:A→E)(s:A→Prop)[DecidablePred s](h:Summable f) : Summable (fun i=> if s i then f i else 0):= by
   convert h.indicator (setOf s) using 1; ext1 x; by_cases hx:s x <;> simp [hx]
lemma push_comp (q:B→C) (f:A→E) (h:Summable f) : push (q ∘ p) f= push q (push p f):= by
   funext x
   let F(i:A) := if q (p i)=x then f i else 0
   rw [push_if]; change (∑' i,F i)=_
   rw [← push_all p (show Summable F from support f _ h), push_if]; refine tsum_congr fun i=>?_ ; by_cases hi:q i=x
   · rw [if_pos hi]; unfold push; exact tsum_congr fun k=> if_pos (by rw [show p k.val=i from k.property, hi] : q (p k.val)=x) -- parse
   rw [if_neg hi,push,show (fun j : p ⁻¹' {i}=> F j.val)=fun _=>(0:E) from funext fun j=> if_neg (fun he=> hi (by rw [← show p j.val=i from j.property]; exact he)),tsum_zero]
omit [CompleteSpace E] in
lemma push_same (q:A→B)(f:A→E)(h:∀ i,f i ≠ 0 → p i=q i): push p f= push q f:= by
   funext x; rw [push_if,push_if]; apply tsum_congr; intro i; by_cases hi:f i=0
   · rw [hi]; simp
   rw [h i hi]
lemma push_plus (f g:A→E)(hf:Summable f)(hg:Summable g): push p (fun i=> f i+g i)=push p f+push p g := funext fun _=> (hf.comp_injective Subtype.val_injective).tsum_add (hg.comp_injective Subtype.val_injective)
lemma push_sub (f g:A→E)(hf:Summable f)(hg:Summable g): push p (fun i=> f i-g i)=push p f-push p g := funext fun _=> (hf.comp_injective Subtype.val_injective).tsum_sub (hg.comp_injective Subtype.val_injective)
omit [CompleteSpace E] in
lemma push_budget (δ:B→ℝ)(hδ:∀ i,0≤δ i) (f:A→E) (H:Summable (fun i=> ‖f i‖)){b} (h:SumBudget (fun i=>δ (p i)*‖f i‖) b) : SumBudget (fun i=>δ i*‖push p f i‖) b:= by
   let u(a) := δ (p a)*‖f a‖
   apply budget_mono (f:=push p u); swap
   · exact fun _=> mul_nonneg (hδ _) (norm_nonneg _)
   · refine ⟨fun _=>tsum_nonneg fun _=> h.1 _,push_sum _ _ h.2.1,(push_all p h.2.1).le.trans h.2.2⟩ -- order
   intro i; unfold push; apply le_trans (b:=δ i * ∑' j : p ⁻¹' {i}, ‖f j.val‖) (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (H.comp_injective Subtype.val_injective)) (hδ i)); rw [← tsum_mul_left]; exact le_of_eq (tsum_congr fun j=> by unfold u; rw [show p j.val=i from j.property]) -- unfold u tactic

variable {F : Type*} {P : F→ Type*} {Q : F→ Type*}

section finite
variable [Fintype F]
abbrev product (f : (i:F)→P i→ℂ)(x:(i:F)→P i):ℂ:=∏ i,f i (x i)
abbrev Abs {A:Type*} (f : A→ℂ): Prop:= Summable (fun x=> ‖f x‖)
lemma product_budget (f : (i:F)→P i→ ℝ)(C:F→ℝ) (h:∀ i,SumBudget (f i) (C i)) : SumBudget (fun x:(i:F)→P i => ∏ i,f i (x i)) (∏ i,C i):= by
   have ht:=series_prod f (fun i=>(h i).2.1)
   exact ⟨fun _=> Finset.prod_nonneg (fun i _=> (h i).1 _),ht.summable, ht.tsum_eq.le.trans (Finset.prod_le_prod (fun i _=>tsum_nonneg (h i).1) (fun i _=> (h i).2.2))⟩
lemma abs_product (f : (i:F)→ P i→ℂ) (h:∀ i,Abs (f i)) : Abs (product f) := by
   unfold Abs product; simp_rw [norm_prod]; exact (series_prod _ h).summable
-- Cplx product path analogue enough, use norm version preceding
private lemma numbered {n : ℕ} {P : Fin n → Type*} (f : ∀ i,P i→ℂ)(h:∀ i,Abs (f i)): (∑' x,product f x)=∏ i,∑' j,f i j := by
   induction n with
   | zero=>
      simp [product,tsum_fintype]
   | succ n IH=>
      let u:=product f; let G:=Fin.consEquiv P
      have hs:= abs_product f h; let f':=(fun i:Fin n=> f i.succ)
      have hk: Summable (u ∘ G):= G.summable_iff.mpr hs.of_norm
      rw [← G.tsum_eq,← show tsum (u ∘ G)=(∑' x,product f (G x)) from rfl,hk.tsum_prod, Fin.prod_univ_succ, ← IH f' (fun i=>h i.succ)]
      have hz (x:P 0)(w): u (G (x,w))= f 0 x * product f' w:= by simp only [G,Fin.consEquiv_apply,u,product,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]; rfl
      simp_rw [comp_apply,hz,tsum_mul_left,tsum_mul_right]
lemma product_tsum (f : (i:F)→P i→ℂ)(h:∀ i,Abs (f i)): (∑' x, product f x)=∏ i,∑' j,f i j:= by
   let e:= (Fintype.equivFin F).symm
   rw [← (Equiv.piCongrLeft P e).tsum_eq,← e.prod_comp]; refine (tsum_congr ?_).trans (numbered (fun i=> f (e i)) (fun i=> h (e i)))
   intro u; unfold product; rw [← e.prod_comp]; simp only [Equiv.piCongrLeft_apply_apply]
lemma many (f : (i:F)→ P i→ℂ)(K : (i:F)→P i→Q i) (h:∀ i,Abs (f i)): push (fun x i=> K i (x i)) (product f)= product (fun i=>push (K i) (f i)):= by
   funext x
   let U : ∀ i,P i→ℂ:= fun i j=> if K i j=x i then f i j else 0
   have he(i): Abs (U i) := by
      unfold Abs U; simp_rw [apply_ite (‖·‖),norm_zero]; exact support _ _ (h i)
   have hx(d): (if (fun i:F=> K i (d i))=x then product f d else 0)= product U d:= by
      split_ifs with hx
      · exact Finset.prod_congr rfl fun i _=> (if_pos (congr_fun hx i)).symm
      obtain ⟨i,hi⟩:=Function.ne_iff.mp hx; exact Eq.symm (Finset.prod_eq_zero (Finset.mem_univ i) (show U i (d i)=0 from if_neg hi))
   rw [push_if]; apply (tsum_congr hx).trans; rw [product_tsum U he]; exact Finset.prod_congr rfl fun _ _=> (push_if ..).symm
end finite
end YM.Comparison.RG02.Sky.Flux
