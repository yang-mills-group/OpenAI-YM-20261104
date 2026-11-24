import YM.WilsonCoeffUV.Vacuum.Gain.Inheritance
/-!
# Non-diagonal pricing. Pair tariffs for numerical era h,d/e comparisons
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free
open scoped ContDiff Topology BigOperators
variable {G:Gauge} {V ι α β :Type*}{r i j:ℕ}{L:Side}{A B C D u t s S M' δ:ℝ}

-- unbounded step-marker comparison weight, this is not a metric
section generic
variable [NormedAddCommGroup V]
structure twain (A δ:ℝ)(u v:V):Prop where
   main: ‖u‖≤ A
   side: ‖v‖≤ A
   gap: ‖u-v‖≤ A*δ
variable {x y p q:V}
lemma twain.nn (h:twain A δ x y):0≤A:= (norm_nonneg _).trans h.main
lemma twain.lift (h:twain A δ x y)(he:A≤B)(hp:0≤δ): twain B δ x y:= ⟨h.main.trans he,h.side.trans he,h.gap.trans (mul_le_mul_of_nonneg_right he hp)⟩
lemma twain.one (x:V)(A:ℝ)(hp:0≤δ)(h:‖x‖≤A): twain A δ x x:=⟨h,h,by simp only [sub_self,norm_zero]; exact mul_nonneg ((norm_nonneg _).trans h) hp⟩
lemma twain.add (h:twain A δ x y)(g:twain B δ p q): twain (A+B) δ (x+p) (y+q):=by
   refine ⟨(norm_add_le ..).trans (add_le_add h.main g.main),(norm_add_le ..).trans (add_le_add h.side g.side),?_⟩
   rw [show (x+p)-(y+q)=(x-y)+(p-q) by abel, add_mul]; exact (norm_add_le ..).trans (add_le_add h.gap g.gap)
lemma twain.neg (h:twain A δ x y):twain A δ (-x) (-y):= ⟨by rw [norm_neg]; exact h.main,by rw [norm_neg]; exact h.side,by rw [neg_sub_neg,norm_sub_rev]; exact h.gap⟩
lemma twain.sub (h:twain A δ x y)(g:twain B δ p q): twain (A+B) δ (x-p) (y-q):= by rw [sub_eq_add_neg,sub_eq_add_neg]; exact h.add g.neg
lemma twain.zero (δ:ℝ): twain 0 δ (0:V) 0:= by constructor<;> simp
lemma twain.sum (s:Finset ι){X Y:ι→ V}{A:ι→ℝ}(h:∀ i∈s,twain (A i) δ (X i) (Y i)): twain (∑ i∈s,A i) δ (∑ i∈s,X i) (∑ i∈s,Y i):=by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact twain.zero _
  | @insert i s e ih=> simp_rw [Finset.sum_insert e]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
variable [NormedSpace ℝ V]
lemma twain.μ {p q:ℝ}(h:twain A δ x y)(g:twain B δ p q): twain (2*A*B) δ (p•x) (q•y):=by
    have he: B*A≤ 2*A*B:=by have ht:=mul_nonneg h.nn g.nn; linarith
    refine ⟨by rw [norm_smul]; exact (mul_le_mul g.main h.main (norm_nonneg _) g.nn).trans he,by rw [norm_smul]; exact (mul_le_mul g.side h.side (norm_nonneg _) g.nn).trans he,?_⟩
    rw [show p•x-q•y=(p-q) • x+ q • (x-y) by rw [sub_smul,smul_sub]; abel]; apply (norm_add_le ..).trans
    rw [norm_smul,norm_smul]; apply (add_le_add (mul_le_mul g.gap h.main (norm_nonneg _) ((norm_nonneg _).trans g.gap)) (mul_le_mul g.side h.gap (norm_nonneg _) g.nn)).trans_eq; ring
lemma twain.mul {x y p q:ℝ}(h:twain A δ x y)(g:twain B δ p q): twain (2*B*A) δ (x*p) (y*q):=g.μ h
end generic
section amber
variable [NormedAddCommGroup V]
structure PairA (s B δ:ℝ)(X Y: Ten V (Cloth α) r): Prop where
   pose: Amber terrain s B X
   vale: Amber terrain s B Y
   visit: Amber terrain s (B*δ) (X-Y)
variable {P Q F H: Ten V (Cloth α) r}
lemma PairA.nn (h:PairA s A δ P Q): 0≤ A:=h.pose.1
lemma PairA.up (h:PairA s A δ P Q)(e:A≤B)(p:0≤δ): PairA s B δ P Q:=⟨h.pose.le e,h.vale.le e,h.visit.le (mul_le_mul_of_nonneg_right e p)⟩
lemma PairA.echo (p:Amber terrain s A P)(h:0≤δ): PairA s A δ P P:= ⟨p,p,by rw [sub_self]; exact Amber.zero.le (mul_nonneg p.1 h)⟩
lemma PairA.neg (h:PairA s A δ P Q): PairA s A δ (-P) (-Q):=⟨h.pose.neg,h.vale.neg,by rw [neg_sub_neg,←neg_sub]; exact h.visit.neg⟩
lemma PairA.add (h:PairA s A δ P Q)(e:PairA s B δ F H): PairA s (A+B) δ (P+F) (Q+H):=⟨h.pose.add e.pose,h.vale.add e.vale,by rw [add_sub_add_comm, add_mul]; exact h.visit.add e.visit⟩
lemma PairA.sub (h:PairA s A δ P Q)(e:PairA s B δ F H): PairA s (A+B) δ (P-F) (Q-H):=by rw [sub_eq_add_neg,sub_eq_add_neg]; exact h.add e.neg
lemma PairA.zero : PairA s 0 δ (0:Ten V (Cloth α) r) 0:=⟨Amber.zero,Amber.zero,by rw [sub_zero,zero_mul]; exact Amber.zero⟩
lemma PairA.sum (S:Finset ι){P Q:ι→ Ten V (Cloth α) r}{b:ι→ℝ}(h:∀ i∈S,PairA s (b i) δ (P i) (Q i)): PairA s (∑ i∈S,b i) δ (∑ i∈S,P i) (∑ i∈S,Q i):=by
  classical
  induction S using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact PairA.zero
  | @insert i S e ih=> simp_rw [Finset.sum_insert e]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
variable [NormedSpace ℝ V]
lemma PairA.μ (h:PairA s A δ P Q)(g:twain B δ u t): PairA s (2*A*B) δ (u•P) (t•Q) :=by
    have he : B*A≤ 2*A*B:=by have hh:=mul_nonneg h.nn g.nn; linarith
    refine ⟨(h.pose.smul u).le ((mul_le_mul_of_nonneg_right g.main h.nn).trans he), (h.vale.smul t).le ((mul_le_mul_of_nonneg_right g.side h.nn).trans he),?_⟩
    rw [show u•P-t•Q=(u-t) • P+t • (P-Q) by rw [sub_smul,smul_sub]; abel]; apply ((h.pose.smul (u-t)).add (h.visit.smul t)).le; exact (add_le_add (mul_le_mul_of_nonneg_right g.gap h.nn) (mul_le_mul_of_nonneg_right g.side h.visit.1)).trans_eq (by ring)
lemma PairA.coin (h: PairA s A δ P Q)(c:ℝ): PairA s (|c| *A) δ (c•P) (c•Q):=⟨h.pose.smul c,h.vale.smul c,by rw [mul_assoc,← smul_sub]; exact h.visit.smul c⟩
lemma PairA.pack {P Q:Gen V (Cloth α)}(h:PairA t A δ (P r) (Q r))(he:0≤s)(hp:s/L.val ≤t): PairA s ((Fintype.card (Site L):ℝ)*(A*Real.exp (8*s))) δ (plants L P r) (plants L Q r):=by
    have H: PairA s (A*Real.exp (8*s)) δ (turnTen (panel L α).symm (P r)) (turnTen (panel L α).symm (Q r)):= by
       refine ⟨gather_coast he (h.pose.mono hp), gather_coast he (h.vale.mono hp),?_⟩
       rw [mul_right_comm]; exact gather_coast he (h.visit.mono hp)
    unfold plants; split; next h=> rw [← Nat.cast_smul_eq_nsmul (R:=ℝ),← Nat.cast_smul_eq_nsmul (R:=ℝ)]; simpa only [abs_of_nonneg (by positivity : 0 ≤ (Fintype.card (Site L) : ℝ))] using! H.coin (Fintype.card (Site L):ℝ)
    have he : 1≤ (Fintype.card (Site L):ℝ):= by exact_mod_cast Fintype.card_pos (α:=Site L)
    exact ⟨H.pose.le (le_mul_of_one_le_left H.nn he), H.vale.le (le_mul_of_one_le_left H.nn he), H.visit.le (by rw [mul_assoc (Fintype.card (Site L):ℝ)]; exact le_mul_of_one_le_left H.visit.1 he)⟩
omit [NormedSpace ℝ V] in
lemma PairA.spare {P Q: Ten V (Cloth (α⊕β)) r}(h: PairA s A δ P Q): PairA s A δ (scoop P) (scoop Q):=⟨scrapC h.pose,scrapC h.vale,scrapC h.visit⟩
end amber

-- post ratios matrix fees.
structure Ballast (s A δ:ℝ)(M N: ropes Cover α β): Prop where
   oneP: dragCup terrain s A M
   otherP: dragCup terrain s A N
   between: dragCup terrain s (A*δ) (M-N)

variable {M N: ropes Cover α β}
lemma Ballast.nn (h:Ballast s A δ M N): 0≤ A:= h.oneP.1
lemma Ballast.fee (h:Ballast s A δ M N)(hp:0≤δ)(e:A≤B): Ballast s B δ M N:=⟨h.oneP.le e,h.otherP.le e,h.between.le (mul_le_mul_of_nonneg_right e hp)⟩
lemma Ballast.mono (h:Ballast s A δ M N)(he:t≤s): Ballast t A δ M N:= ⟨h.oneP.mono he,h.otherP.mono he,h.between.mono he⟩
lemma Ballast.zero : Ballast s 0 δ (0:ropes Cover α β) 0:=⟨dragCup.zero, dragCup.zero,by rw [sub_zero,zero_mul]; exact dragCup.zero⟩
lemma Ballast.same (h: dragCup terrain s A M)(p:0≤δ): Ballast s A δ M M:=⟨h,h,by rw [sub_self]; exact dragCup.zero.le (mul_nonneg h.1 p)⟩
lemma Ballast.up {G H: ropes Cover α α}(h:Ballast s B δ G H)(p:Ballast s B δ M N): Ballast s B δ (upper G M) (upper H N):=by
    have he: upper G M-upper H N=upper (G-H) (M-N):=by ext1 i j; obtain ⟨v,b|b⟩:= j <;>rfl
    refine ⟨?_,?_,?_⟩; exact (upper_cap h.oneP p.oneP).le (max_le le_rfl le_rfl); exact (upper_cap h.otherP p.otherP).le (max_le le_rfl le_rfl); rw [he]; exact (upper_cap h.between p.between).le (max_le le_rfl le_rfl)
lemma Ballast.staged {G H: ropes Cover ι β}(h:Ballast s B δ M N)(p:Ballast s B δ G H): Ballast s B δ (stair M G) (stair N H):=by
   have he: stair M G-stair N H=stair (M-N) (G-H):=by ext1 i j; obtain ⟨v,b|b⟩:=i <;>rfl
   refine ⟨?_,?_,?_⟩; exact (strafe h.oneP p.oneP).le (max_le le_rfl le_rfl); exact (strafe h.otherP p.otherP).le (max_le le_rfl le_rfl); rw [he]; exact (strafe h.between p.between).le (max_le le_rfl le_rfl)

-- star, convolution bound closed form.
section
variable [Fintype α][NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]

def tieN (α:Type*)[Fintype α](s:ℝ) (r:ℕ):ℝ:= if r=0 then 1 else tiePay α r s
omit [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
lemma tieN_nn (p:0<s)(r:ℕ):0≤tieN α s r:=by
   unfold tieN; split; positivity
   next hg=> exact pow_nonneg (boardPay_nn (div_pos p (by positivity))) _
lemma PairA.prune_bill {M N : ropes Cover α β} (h:Ballast t B δ M N)(_hc:0≤δ)(ht:s<t)(hs:0≤s){P Q: Gen V (Cloth α)}(e:PairA t C δ (P r) (Q r)): PairA s ((r+1:ℕ)*B^r*C*tieN α (t-s) r) δ (prism M P r) (prism N Q r):=by
   have hv:=h.nn; have hx:=e.nn; have hy:=tieN_nn (α:=α) (sub_pos.mpr ht) r
   cases r with
   | zero=>
     simp only [Nat.zero_add,Nat.cast_one,pow_zero,mul_one,one_mul,tieN,↓reduceIte]
     exact ⟨reflect_eta h.oneP e.pose hs ht,reflect_eta h.otherP e.vale hs ht,reflect_gap h.otherP h.oneP h.between e.vale e.pose e.visit hs ht⟩
   | succ r=>
     simp_rw [tieN, if_neg (Nat.succ_ne_zero _)] at *
     have hh : B^(r+1)*C * tiePay α (r+1) (t-s) ≤ ((r+1+1:ℕ):ℝ)*B^(r+1)*C*tiePay α (r+1) (t-s):= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) (by exact_mod_cast Nat.le_add_left 1 _)) hx) hy
     refine ⟨?_,?_,?_⟩
     · have he := reflect_eta h.oneP e.pose hs ht; rw [if_neg (Nat.succ_ne_zero _)] at he; exact he.le hh
     · have he:= reflect_eta h.otherP e.vale hs ht; rw [if_neg (Nat.succ_ne_zero _)] at he; exact he.le hh
     have he:= reflect_gap h.otherP h.oneP h.between e.vale e.pose e.visit hs ht; rw [if_neg (Nat.succ_ne_zero _),Nat.add_sub_cancel] at he; apply he.le; apply le_of_eq; push_cast; rw [pow_succ]; ring

-- rank factors costs

def fareV (r:ℕ) : ℝ:= (1/2:ℝ)*(r+1:ℕ)*(r+2:ℕ)
lemma crimp_cap {M N: ropes Cover α α}{P Q:Gen V (Cloth α)} (h:Ballast s B δ M N)(_hc:0≤δ)(he:t<s)(hp:0≤t)(g:PairA s A δ (P (r+2)) (Q (r+2))): PairA t (2*B*A*fareV r*tiePay α 2 (s-t)) δ (crimp M P r) (crimp N Q r):=by
   let S:= tiePay α 2 (s-t); let K:= fareV r; have hk:0≤K:= by unfold K fareV; positivity
   have hs:0≤ S:= by have H:= tieN_nn (α:=α) (sub_pos.mpr he) 2; exact H
   have hb:= h.nn; have ha:= g.nn
   have hv : B*A*K*S≤ 2*B*A*K*S:= by gcongr; linarith
   have HH := rain_bill h.oneP g.pose (hp.trans he.le); have H':= rain_bill h.otherP g.vale (hp.trans he.le)
   refine ⟨(worn_amber HH hp he).le hv, (worn_amber H' hp he).le hv,?_⟩
   rw [crimp,crimp, ← worn_sub HH H' (lt_of_le_of_lt hp he)]; apply (worn_amber (rain_gap h.oneP h.between g.visit g.vale (hp.trans he.le)) hp he).le; unfold fareV; exact le_of_eq (by ring)
def pegPrice (r t: ℕ) : ℝ:= (1/2:ℝ)*(r+1:ℕ)*(t+1:ℕ)
lemma loop_cap {M N: ropes Cover α α}{P Q:Gen ℝ (Cloth α)}{F H: Gen V (Cloth α)}(h:Ballast s B δ M N)(_hc:0≤δ)(he:t<s)(hp:0≤t) (g:PairA s A δ (P (i+1)) (Q (i+1))) (hg:PairA s C δ (F (j+1)) (H (j+1)))(ha:i+j=r): PairA t (3*pegPrice i j * B * A * C * tiePay α 2 (s-t)) δ (worn (swivel (rill M P F r i j))) (worn (swivel (rill N Q H r i j))) := by
   let Z:= pegPrice i j; let T:= tiePay α 2 (s-t); have ht : 0≤ T:= by have H:=tieN_nn (α:=α) (sub_pos.mpr he) 2; exact H;
   have he':0≤Z:=by unfold Z pegPrice; positivity
   have hb:=h.nn; have hB:=g.nn; have hC:=hg.nn
   have H0 := swivel_cup (rill_bill h.oneP g.pose hg.pose (hp.trans he.le) ha); have H1:=swivel_cup (rill_bill h.otherP g.vale hg.vale (hp.trans he.le) ha)
   have hv : Z*B*A*C*T ≤ 3*Z*B*A*C*T:= by gcongr; linarith
   refine ⟨(worn_amber H0 hp he).le hv,(worn_amber H1 hp he).le hv,?_⟩
   rw [← worn_sub H0 H1 (lt_of_le_of_lt hp he)]; apply (worn_amber (swivel_gap (rill_gap h.otherP h.between g.pose hg.pose hg.visit g.vale g.visit (hp.trans he.le) ha)) hp he).le; unfold pegPrice; exact le_of_eq (by ring)
end
end YM.WilsonCoeffUV.Bank
