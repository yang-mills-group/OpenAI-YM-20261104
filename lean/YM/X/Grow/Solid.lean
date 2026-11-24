import YM.X.Reed.Pass
import YM.Next.RANK.ScaleScale
/-!
# weighted polynomials below-&-above workhorse
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Grow
open MvPolynomial Function Lattice Next.Rank Normal LiftMark Maxwell Finset
open scoped Topology Classical Pointwise
variable {V W I:Type*} {w:V→ℕ}{u:W→ℕ}{i j k m:ℕ}
def strongL(w:V→ℕ)(i:ℕ) : Submodule ℂ (poly V):= restrictSupport ℂ {a|i≤ Finsupp.weight w a}
-- ergonomic Prop, alias
abbrev Strong (w:V→ℕ)(i:ℕ)(p:poly V):Prop:=p ∈ strongL w i
variable {p q p' q':poly V}
lemma sturdy : Strong w i p↔ ∀ x∈p.support,i≤ Finsupp.weight w x:=(mem_restrictSupport_iff ℂ)
namespace Strong
lemma zero : Strong w i (0:poly V):= (strongL w i).zero_mem
lemma add (h:Strong w i p)(g:Strong w i q):Strong w i (p+q):=(strongL w i).add_mem h g
lemma sub (h:Strong w i p)(g:Strong w i q):Strong w i (p-q):=(strongL w i).sub_mem h g
lemma scale (h:Strong w i p)(a:ℂ): Strong w i (a • p):= (strongL w i).smul_mem a h
lemma sum (p:Finset I){f:I→poly V}(h:∀ i'∈p, Strong w i (f i')): Strong w i (∑ x∈p,f x):=(strongL w i).sum_mem h
lemma atom (p0 : V→₀ℕ)(b:ℂ): Strong w (Finsupp.weight w p0) (MvPolynomial.monomial p0 b):= sturdy.mpr (fun x hx=> (eq_of_mem_singleton (support_monomial_subset hx)) ▸ le_rfl) -- variables below
lemma first : Strong w 0 p:= sturdy.mpr (fun x _=> Nat.zero_le _)
lemma rung (z:V): Strong w (w z) (MvPolynomial.X z):= by apply sturdy.mpr; intro x hx; simp only [MvPolynomial.support_X, mem_singleton] at hx; rw [hx,Finsupp.weight_single]; simp
lemma weaken (h:Strong w i p)(h':k ≤ i):Strong w k p:= sturdy.mpr (fun x hx=> h'.trans (sturdy.mp h x hx))
lemma after (p:poly V)(i:ℕ) : Strong w (i+1) (p-level w i p):= by
   apply sturdy.mpr; intro x hx; have ht:= mem_support_iff.mp hx; simp only [coeff_sub] at ht; change coeff x p-coeff x (Rise.trim p w i)≠0 at ht; rw [Rise.trim_coeff] at ht; split at ht <;> simp at ht <;> omega
lemma none (h:Strong w i p)(hi:k < i) : level w k p=0:= by
   ext x; change coeff x (Rise.trim p _ _)=_; rw [Rise.trim_coeff];by_cases hp:x∈p.support; · have he:=sturdy.mp h x hp; rw [if_neg (by omega),coeff_zero]
   simp [MvPolynomial.notMem_support_iff.mp hp]
lemma undo (h:level w i p=0): Strong w (i+1) p:= by simpa [h] using after (w:=w) p i
lemma head (h:Strong w i p):Strong w i (level w i p):= by
   have ht := (h.sub ((after (w:=w) p i).weaken i.le_succ)); rwa [sub_sub_self] at ht
lemma multiply (h:Strong w i p)(p':Strong w k q):Strong w (i+k) (p*q):=by
   apply sturdy.mpr; intro x hx; obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp (MvPolynomial.support_mul p q hx); rw [map_add]; exact Nat.add_le_add (sturdy.mp h a ha) (sturdy.mp p' b hb)
lemma pow (h:Strong w i p)(n:ℕ): Strong w (n*i) (p^n):= by induction n with
     | zero=>rw [Nat.zero_mul];apply first
     | succ n ih=> rw [add_mul,one_mul,pow_succ]; exact ih.multiply h
lemma prod (s:Finset I)(f:I→ℕ)(g:I→poly V)(h:∀i∈s, Strong w (f i) (g i)): Strong w (∑ i∈s,f i) (∏ i∈s,g i):= by
   induction s using Finset.induction_on with
   | empty=> rw [sum_empty];apply first
   | insert i s hi IH=> rw [sum_insert hi,prod_insert hi]; exact (h i (mem_insert_self ..)).multiply (IH (fun b hb=>h b (mem_insert_of_mem hb)))
lemma of_pure (h : MvPolynomial.IsWeightedHomogeneous w p i) : Strong w i p:= sturdy.mpr (fun x hx=> le_of_eq (h (mem_support_iff.mp hx)).symm)
end Strong
variable {s t: V →₀ ℕ}
variable {a b:ℂ}
abbrev levelJob(w:V→ℕ)(p p':poly V)(i:ℕ): Prop:=level w i p=level w i p'
lemma multiply_equality (h:Strong w i p) (hp:Strong w i p') (g:Strong w k q) (ht:Strong w k q')(he:levelJob w p p' i)(ht':levelJob w q q' k):levelJob w (p*q) (p'*q') (i+k):=by
    have h₀:Strong w (i+1) (p-p'):= Strong.undo (by rw [map_sub,he,sub_self])
    have h₁:Strong w (k+1) (q-q'):= Strong.undo (by rw [map_sub,ht',sub_self]);
    apply sub_eq_zero.mp; rw [← map_sub,show p*q-p'*q'=(p-p')*q+p'*(q-q') by ring,map_add]; rw [(h₀.multiply g).none (by omega),(hp.multiply h₁).none (by omega),zero_add]
lemma pow_equality (h:Strong w i p)(hp:Strong w i p')(hx:levelJob w p p' i)(n:ℕ):levelJob w (p^n) (p'^n) (n*i):=by
   induction n with
   | zero=> rw [pow_zero,pow_zero]
   | succ n IH=> rw [pow_succ,pow_succ,add_mul,one_mul];exact multiply_equality (h.pow n) (hp.pow n) h hp IH hx
lemma prod_equality (f g:I→poly V) (s:I→ℕ) (b:Finset I)(h:∀i∈b, Strong w (s i) (f i))(hp:∀i∈b,Strong w (s i) (g i))(hx:∀i∈b,levelJob w (f i) (g i) (s i)):
    levelJob w (∏ i∈b,f i) (∏ i∈b,g i) (∑ i∈b,s i):=by
   induction b using Finset.induction_on with
   | empty=> rw [prod_empty,prod_empty]
   | insert i b hi IH=> rw [sum_insert hi,prod_insert hi,prod_insert hi]; exact multiply_equality (h i (mem_insert_self ..)) (hp i (mem_insert_self ..)) (Strong.prod b s f (fun i hh=>h _ (mem_insert_of_mem hh))) (Strong.prod b s g (fun i hh=>hp _ (mem_insert_of_mem hh))) (hx _ (mem_insert_self ..)) (IH (fun i hh=>h _ (mem_insert_of_mem hh)) (fun i hh=> hp _ (mem_insert_of_mem hh)) (fun i hh=> hx _ (mem_insert_of_mem hh)))
abbrev Raises(w:V→ℕ)(u:W→ℕ)(F:poly V→ₐ[ℂ] poly W):Prop:= ∀ z,Strong u (w z) (F (X z)) -- ambiguity
lemma Raises.atom {F:poly V→ₐ[ℂ] poly W}(h: Raises w u F)(t: V→₀ℕ)(b:ℂ) : Strong u (Finsupp.weight w t) (F (MvPolynomial.monomial t b)) := by
   rw [MvPolynomial.monomial_eq,map_mul,map_finsuppProd,Finsupp.weight_apply]; rw [show F (C b)=C b from F.commutes _];unfold Finsupp.sum Finsupp.prod -- check map_finsupp
   nth_rw 1 [show ∑ i∈t.support,t i • w i= 0+∑ i∈t.support,t i • w i from (zero_add _).symm]; refine Strong.first.multiply (Strong.prod _ _ _ ?_); intro i hi; simp only [map_pow]; exact (h i).pow _
lemma Raises.feed {F:poly V→ₐ[ℂ] poly W}(h:Raises w u F)(hp:Strong w i p):Strong u i (F p):=by
    nth_rw 1 [p.as_sum]; rw [map_sum]; exact Strong.sum p.support (fun x hx=> (h.atom x _).weaken (sturdy.mp hp x hx))
def Ready (w:V→ℕ) (u:W→ℕ)(F G:poly V→ₐ[ℂ] poly W):Prop:= ∀ z,levelJob u (F (X z)) (G (X z)) (w z)
lemma Ready.atom {F G:poly V→ₐ[ℂ] poly W}(h:Ready w u F G) (hf:Raises w u F)(hp:Raises w u G)(i:V→₀ℕ)(a:ℂ): levelJob u (F (MvPolynomial.monomial i a)) (G (MvPolynomial.monomial i a)) (Finsupp.weight w i):=by
   rw [MvPolynomial.monomial_eq,map_mul,map_mul,show F (C a)=C a from F.commutes _,show G (C a)=C a from G.commutes _]; unfold Finsupp.prod; rw [map_prod,map_prod,Finsupp.weight_apply,Finsupp.sum]; simp_rw [map_pow]; nth_rw 1 [show ∑ j∈i.support,i j • w j= 0+∑ j∈i.support,i j • w j from (zero_add _).symm]; refine multiply_equality Strong.first Strong.first (Strong.prod _ _ _ ?_) (Strong.prod _ _ _ ?_) rfl ?_; swap
   · intro z _; exact (hp z).pow (i z)
   · intro z _; exact (hf z).pow (i z) -- order fails
   · exact prod_equality _ _ _ _ (fun z _=> (hf z).pow (i z)) (fun z _=> (hp z).pow (i z)) (fun z _=>pow_equality (hf z) (hp z) (h z) (i z))
lemma Ready.feed {F G:poly V→ₐ[ℂ] poly W} (h:Ready w u F G)(hf:Raises w u F)(hp:Raises w u G)(hg: Strong w i p): levelJob u (F p) (G p) i:=by
   unfold levelJob; rw [p.as_sum,map_sum,map_sum,map_sum,map_sum]
   apply Finset.sum_congr rfl; intro a ha
   rcases lt_or_eq_of_le (sturdy.mp hg a ha) with h'|hb
   · rw [(hf.atom a _).none h',(hp.atom a _).none h']
   exact hb ▸ h.atom hf hp a _ -- direction?
lemma Raises.trim {F:poly V→ₐ[ℂ] poly W}(h: Raises w u F) : levelJob u (F (level w i p)) (F p) i:= by apply sub_eq_zero.mp; rw [←neg_inj,neg_sub,← map_sub,←map_sub, (h.feed (Strong.after ..)).none (by omega), neg_zero]
end YM.PositionX.Grow
