import YM.OPE.Compatible.Parcels.Halt
/-!
# Weighted Taylor on rays including long b. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG
open scoped Topology BigOperators Classical
variable {I J: Type*}[Fintype I][DecidableEq I]{Y:Type*}[NormedAddCommGroup Y] {w:J→ℝ}
private lemma bounded_line {f:Shift I→J→Y}{c:ℝ}{k:ℕ} (he:0≤w)(h:f 0=0)(hh:∀ (x:Shift I),size x≤ k→∀ i,Sack w (numDiff i f x) c)(x: Shift I)(hp:size x≤ k): Sack w (f x) ((size x:ℝ)*c):=by
   generalize ha:size x=n at * -- dangerous
   induction n using Nat.strong_induction_on generalizing x with | h n ih
   by_cases hf:x=0
   · subst x; rw [h,← ha,show size (0:Shift I)=0 by simp [size]]; simp only [Nat.cast_zero,zero_mul]; exact Sack.zero le_rfl _
   obtain ⟨i,y,hl,hx⟩:=stride x hf; rw [ha] at hl; have h' : size y<n:=by omega
   have hz:= ih (size y) h' y rfl (by omega)
   rcases hx with hx|hx; subst x
   · have ht:=hh y (by omega) i; change Sack w (f (y+stint i)-f y) c at ht; have hg:=ht.splits hz he; rw [sub_add_cancel] at hg; apply hg.tips; rw [hl]; push_cast; linarith only
   subst x; have ht:= hh (y-stint i) (by omega) i; change Sack w (f (y-stint i+stint i)-_) c at ht; rw [sub_add_cancel] at ht; have hg:= hz.subsumes ht he; rw [sub_sub_cancel] at hg -- maybe not fact
   apply hg.tips; rw [hl]; push_cast; linarith only
-- estimate size^d
lemma polynomial_walk {f:Shift I→J→Y} (d:ℕ){c:ℝ}{k:ℕ}(hc:0≤ c) (he:0≤w) (h:∀ l:List I,l.length<d→ dvol l f 0=0)
    (hh:∀ (l:List I),l.length=d→∀ x,size x≤ k→Sack w (dvol l f x) c)(x:Shift I)(hp:size x≤ k): Sack w (f x) ((size x:ℝ)^d * c):=by
   induction d generalizing x f with
   | zero=> have hx:=hh [] rfl x hp; simpa only [dvol,pow_zero,one_mul] using hx
   | succ d ih=>
     have hz(i:I)(y:Shift I)(ht:size y ≤ size x): Sack w (numDiff i f y) ((size x:ℝ)^d*c):=by
        refine (ih (f:=numDiff i f) (fun l hl=>?_) (fun l hl v hv=>?_) y (ht.trans hp)).tips (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by exact_mod_cast ht) d) hc)
        · rw [← rotate_tail]; exact h (i::l) (by simpa using hl)
        rw [← rotate_tail]; exact hh (i::l) (by simp [hl]) v hv
     apply (bounded_line he (h [] (by simp)) (fun y hy i=>hz i y hy) x le_rfl).tips; exact le_of_eq (by ring)
-- sketch value m^k bound for any pos
lemma pine_paths (i:Multiset I)(x:Shift I): ‖pine i x‖ ≤ (size x:ℝ)^i.card := by
    let f (j:Shift I): Unit → ℝ:= fun _=> pine i j
    have he(l:List I) (p:Shift I): dvol l f p=dvol l (pine i) p • (1:Unit→ℝ):=by
        rw [show f=(fun x=> pine i x • (1:Unit→ℝ)) by ext; simp [f]]; exact slot_run _ _ _ _
    have ht(l:List I)(h:i.card=l.length): ∀ (p:Shift I),dvol l (pine i) p=dvol l (pine i) 0:=by
        intro p; generalize hx:size p=n; induction n using Nat.strong_induction_on generalizing p with | h n ih
        by_cases he:p=0; rw [he]
        obtain ⟨j,q,hq,hp⟩:= stride p he; rw [hx] at hq; have hs : size q < n:=by omega
        have hy:= ih (size q) hs q rfl
        have hi:= overrun i (j::l) (by rw [List.length_cons]; omega); rw [← hy]; rcases hp with g|g <;> subst p
        · exact sub_eq_zero.mp (congr_fun hi q)
        have hh: dvol l (pine i) (q-stint j+stint j)-dvol l (pine i) (q-stint j)=0:= congr_fun hi _; rw [sub_add_cancel] at hh; exact (sub_eq_zero.mp hh).symm
    have h : 1*‖f x ()‖≤ (size x:ℝ)^i.card*1:= by
       refine (polynomial_walk (k:=size x) i.card (c:=1) zero_le_one (w:=fun _=>1) (fun _=>zero_le_one) ?_ ?_ x le_rfl).single ()
       · intro l hl; rw [he,known, if_neg ?_,zero_smul]; intro hx; apply (Nat.ne_of_lt hl); simp only [← hx,Multiset.coe_card]
       intro l hl y _; rw [he,ht _ hl.symm y,known]; split
       · rw [one_smul]; simp [Sack,SumBudget]; exact (hasSum_fintype _).summable
       rw [zero_smul]; exact Sack.zero zero_le_one _
    simpa only [f,one_mul,mul_one] using h
variable [NormedSpace ℝ Y]
-- supply at radius x>=L big
lemma long_sketch {f:Shift I→ J→ Y}{L U:ℝ}{n m:ℕ}(h:n≤ m)(hx:1 ≤ L)(hp:0≤ U)(hw:0≤ w)
    (hz:∀ l: List I,l.length<n→ Sack w (dvol l f 0) (U/L^l.length)) (x:Shift I) (he:L ≤ size x): Sack w (sketch n f x) ((trail I n).card *((size x:ℝ)/L)^m *U):=by
    have hq: 0 < L:=by linarith
    unfold sketch; rw [Finset.sum_apply]; apply (Sack.finGather (B:=fun _=> ((size x:ℝ)/L)^m*U) _ (fun i=>pine i x • dvol i.toList f 0) ?_ hw).tips (by simp;ring_nf; exact le_rfl)
    intro i hi; have hv:= (trailed i n).1 hi; have ha:i.toList.length=i.card:= Multiset.length_toList ..
    apply ((hz i.toList (ha.trans_lt hv)).scale_line (pine i x)).tips; rw [ha]; calc
       _ ≤ (size x:ℝ)^i.card * (U/L^i.card):= mul_le_mul_of_nonneg_right (pine_paths i x) (by positivity)
       _ = ((size x:ℝ)/L)^i.card*U:=by rw [div_pow]; ring
       _ ≤ _:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ((one_le_div hq).2 he) (hv.le.trans h)) hp
end YM.OPE.Flume
