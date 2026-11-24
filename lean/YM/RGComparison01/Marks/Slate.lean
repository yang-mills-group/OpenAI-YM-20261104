import YM.MergeProof.SwitchCost
/-!
# Triangular accumulation estimator for a shape-wide real switch family

 Uses the pinned ring semantics (`Switch.jet` at x→0+) after continuation
 in an independent, *real* activation parameter. Will permit Cauchy bounds
 on the genuinely summed auxiliary total without a complex log estimate.
 Factorial convention is recorded to enable comparison downstream. This
 is *local at the unnormalized step*; the moment U in application is always
 the quotient by the field-dependent conditional push.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Slate
open Function Filter Finset MeasureTheory Merge Switch Marker GridRenewal.Rain
open scoped Topology ContDiff BigOperators Classical
variable {ι:Type} {α : Type} {p: Finset ι} {H J:Score ι} {f g : Ways ι} {d C:ℝ}{n : ℕ}
variable [Fintype ι]
omit [Fintype ι] in
lemma bottom {F:Ways ι} (h: Models F g) : jet F ∅ = F 0 ∅:= by
  rw [h.exact,← h.current 0 ⟨le_rfl,zero_le_one⟩]; simp only [Switch.value,powerset_empty,sum_singleton,card_empty,pow_zero,one_mul]
lemma times (h : Paid (fun _:Unit=>f) d)(he:Paid (fun _:Unit=>g) C) : jet (f*g)=comb 0 (jet f) (jet g):=by
  obtain ⟨g',hg⟩:= h.works (); obtain ⟨f',hf⟩:= he.works (); rw [show jet f=g' 0 from hg.exact,show jet g=f' 0 from hf.exact]; exact (show Models (f*g) _ from hg.mul hf).exact
lemma family (s:Finset α)(f:α→Ways ι)(u:α→ℝ)(h: ∀ i∈s,Paid (fun _:Unit=>f i) (u i)): jet (∑ i∈s,f i)=∑ i∈s,jet (f i):= by
   induction s using Finset.induction_on with
   | empty => simp_rw [sum_empty]; rw [show (0:Ways ι)=click ∅ 0 from funext fun _=> funext fun _=> (by simp [click]),(modelClick _ _).exact]; ext p; simp [bench]
   | insert i s hi ih=>
     have hf':= fun i (hp:i∈s)=> h i (mem_insert_of_mem hp)
     rw [sum_insert hi,sum_insert hi,← ih hf']; obtain ⟨g,hg⟩:= (h i (mem_insert_self ..)).works ()
     have hz := Paid.sum s (fun i (_:Unit)=> f i) u hf'; obtain ⟨k,hk⟩:= hz.works (); simp only [Finset.sum_apply] at hk
     have hg : Models (f i) g:= hg; rw [(hg.add hk).exact,hg.exact,hk.exact]; rfl

def stack (F:Score ι): ℕ → Score ι
  | 0=> bench ∅ 1
  | n+1 => comb 0 (stack F n) F
lemma stack_power (i:ℕ) (h:Paid (fun _:Unit=> f) d) : jet (f^i)=stack (jet f) i:= by
   induction i with
   | zero=>rw [pow_zero, stack, show (1:Ways ι)=click ∅ 1 from funext fun _=> funext fun _=> (by simp [click]),(modelClick _ _).exact]
   | succ i ih=> rw [pow_succ, stack,times (f:=f^i) (show Paid (fun _:Unit=> f^i) (d^i) from h.pow i) h,ih]
-- nil comb support law, ambient instance using Classical
lemma flesh (f g:Score ι) (p: Finset ι) : comb 0 f g p=∑ z:Finset ι × Finset ι,
    if p=z.1∪z.2 ∧ Disjoint z.1 z.2 then f z.1 *g z.2 else 0:= by
  apply Finset.sum_congr rfl; intro z _; by_cases h:p=z.1∪z.2
  · by_cases hx:Disjoint z.1 z.2
    · rw [if_pos h,if_pos ⟨h,hx⟩,Finset.disjoint_iff_inter_eq_empty.mp hx,card_empty,pow_zero,one_mul]
    have h0 : (z.1∩z.2).card≠0 := fun hi=>hx (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hi))
    rw [if_pos h,if_neg (fun hh=> hx hh.2),zero_pow h0,zero_mul,zero_mul]
  rw [if_neg h,if_neg (fun hx=> h hx.1)]

lemma comb_left (c:ℝ)(F : Score ι)(i:Finset ι): comb 0 (bench ∅ c) F i=c*F i:= by
   rw [flesh,sum_eq_single_of_mem (∅,i) (mem_univ _)]
   · simp only [empty_union,disjoint_empty_left, true_and, if_true, bench] -- names inspect
   intro j _ h; split
   next hv=>
     rw [show bench ∅ c j.1=0 from ?_,zero_mul]
     exact if_neg (fun hp=> h (Prod.ext hp (Eq.symm (by simpa [hp] using hv.1))))
   next=> rfl
lemma stack_one (F:Score ι): stack F 1=F:= by
  ext i; rw [stack,stack,comb_left,one_mul]
lemma struck (n:ℕ) (hH : H ∅=0) (p:Finset ι) (hp:p.card < n): stack H n p=0:= by
   induction n generalizing p with
   | zero=> exact (Nat.not_lt_zero _ hp).elim
   | succ n ih=>
     rw [stack,flesh]; refine sum_eq_zero fun i _=> ?_; split
     next h=>
       by_cases hx:i.2=∅; rw [hx,hH,mul_zero]
       have hv:= card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hx); have hz:=h.2
       rw [h.1,card_union_of_disjoint hz] at hp; rw [ih i.1 (by omega),zero_mul]
     next=> rfl

lemma belongs (H J:Score ι) (p:Finset ι)(hi : ∀ i⊆p,H i=J i) (n:ℕ): stack H n p= stack J n p:= by
   induction n generalizing p with
   | zero=>rw [stack, stack]
   | succ i ih=>
     rw [stack,flesh,stack,flesh]; apply Finset.sum_congr rfl; intro t _; split
     next h=>exact congr_arg₂ (·*·) (ih _ fun i hu=>hi i (h.1.symm ▸ hu.trans subset_union_left)) (hi _ (h.1.symm ▸ subset_union_right))
     next=>rfl
lemma collegiate (n:ℕ) (hh: H ∅=0)(he:J ∅=0) (h:∀ i ⊂ p,H i=J i): stack H (n+2) p=stack J (n+2) p:=by
  rw [stack.eq_2 H, stack.eq_2 J, flesh, flesh]; apply Finset.sum_congr rfl; intro j _; split
  next hz=>
    have hy:= card_union_of_disjoint hz.2; rw [← hz.1] at hy
    by_cases hx:j.2=∅; rw [hx,he,hh,mul_zero,mul_zero]
    have hp:= card_pos.mpr (nonempty_iff_ne_empty.mpr hx)
    by_cases hm:j.1=∅
    · rw [hm,struck (n+1) hh _ (by simp),struck (n+1) he _ (by simp),zero_mul,zero_mul]
    have hP:= card_pos.mpr (nonempty_iff_ne_empty.mpr hm)
    have hk : j.1 ⊂ p:= (ssubset_iff_subset_ne).2 ⟨hz.1.symm ▸ subset_union_left,fun hq=>by rw [hq] at hy; omega⟩
    have hk' : j.2 ⊂ p:= (ssubset_iff_subset_ne).2 ⟨hz.1.symm ▸ subset_union_right,fun hq=>by rw [hq] at hy; omega⟩
    exact congr_arg₂ (·*·) (belongs H J _ (fun i hi=> h i (Finset.ssubset_of_subset_of_ssubset hi hk)) _) (h _ hk')
  next=> rfl
variable (h:Paid (fun _:Unit=>f) d)
include h
local notation "ℙ"=> Fintype.card ι
local notation "Z"=> jet (fun i p=> Real.exp (f i p))
local notation "E"=> jet f
abbrev levy (i:ℕ):= ((i.factorial:ℝ)⁻¹)
lemma stratum (n:ℕ) (p:Finset ι) : jet (fun i p=> slide (f i p) n) p=levy n*stack E n p := by
   let c:= levy n; let g:Ways ι:= fun _ _=> c
   have hx:Paid (fun _:Unit=>g) ‖c‖:= Switch.constant _ (norm_nonneg _) (fun _=> le_rfl)
   rw [show (fun i p=> slide (f i p) n)= g*f^n from funext fun _=> funext fun _=> (by simp only [g,c,levy,slide,div_eq_mul_inv, Pi.mul_apply, Pi.pow_apply,mul_comm]), times hx (show Paid (fun _:Unit=>f^n) (d^n) from h.pow n), stack_power n h,show g=click ∅ c from (by ext;simp [click,g]),(modelClick _ _).exact,comb_left]
lemma rack (h0:f 0 ∅=0) (m:ℕ) (hm:ℙ≤m) (p:Finset ι): Z p=∑ i∈range (1+m+2),levy i*stack E i p:= by
   have he : HasSum (fun i=> levy i*stack E i p) (Z p):=by
     simp_rw [← stratum h]; have hp:=fun n=> paidTerms n h; have hV := Switch.issue hp (meter d).summable; simp_rw [show ∀ (u:ℝ),(∑' i,slide u i)=Real.exp u from fun _=>(meter _).tsum_eq] at hV; exact hV.2 () p
   rw [←he.tsum_eq]; refine tsum_eq_sum fun i h'=>?_ ; refine mul_eq_zero_of_right _ (struck i (bottom ((h.works ()).choose_spec)|>.trans h0) p ?_); have ht:= (card_le_univ p).trans hm; have hk:= not_lt.mp (mt mem_range.mpr h'); omega
lemma solo (h0:f 0 ∅=0) (m:ℕ) (hm:ℙ≤m) (hp:p≠∅) : jet f p= Z p - ∑ i∈Finset.range (m+1),levy (i+2)*stack (jet f) (i+2) p:= by
   rw [rack h h0 m hm p]
   let U i:=levy i*stack E i p; change _= (∑ i∈range (1+m+2), U i)- ∑ i∈ range (m+1),U (i+2)
   have ht₀ : U 0=0:=by unfold U levy; rw [stack, show bench ∅ 1 p=0 from if_neg hp,mul_zero]
   have ht₁ : U 1=E p:=by unfold U; rw [stack_one]; norm_num [levy]
   rw [show 1+m+2=2+(m+1) from (by omega),Finset.sum_range_add U,show (∑ i∈Finset.range (m+1),U (i+2))=_ from (Finset.sum_congr rfl (fun i (_:i∈Finset.range (m+1))=> congr_arg U (show i+2=2+i from Nat.add_comm i _))), add_sub_cancel_right]
   rw [sum_range_succ,sum_range_one,ht₀,ht₁,zero_add]
-- Projection from conditional moments.
def shell (m:ℕ)(H:Score ι): ℕ → Score ι
 | 0 => 0
 | n+1 => fun p=> if p=∅ then 0 else H p - ∑ i∈ Finset.range (m+1), levy (i+2)*stack (shell m H n) (i+2) p
lemma protocol (h0:f 0 ∅=0) (m:ℕ) (hm:ℙ≤m) (n:ℕ) (p:Finset ι) (hp:p.card≤n) : jet f p= shell m Z n p:= by
    have he : jet f ∅=0:= (bottom ((h.works ()).choose_spec)).trans h0
    induction n generalizing p with
    | zero=> rw [show p=∅ from card_eq_zero.mp (Nat.eq_zero_of_le_zero hp),he,shell];rfl
    | succ i ih=>
      simp only [shell]; by_cases hx:p=∅; rw [if_pos hx,hx]; exact he
      rw [if_neg hx]; refine (solo h h0 m hm hx).trans (congr_arg (Z p-·) (Finset.sum_congr rfl (fun j h=> congr_arg (levy (j+2)*·) (collegiate j he ((ih ∅ (by simp)).symm.trans he) (fun k hk=> ih _ (Nat.le_of_lt_succ (lt_of_lt_of_le (Finset.card_lt_card hk) hp)))))))
end YM.RGComparison01.Slate
