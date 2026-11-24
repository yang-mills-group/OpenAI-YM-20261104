import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Trees
/-!
# One-loop crossing

Momenta at root useful for routing. Reversal relation accounts even vacuum, odd left-root ker.
 Here no estimates. Used at cover ∆ even P & odd T. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux
variable {R A P I: Type}[AddCommGroup P][CommRing R][Fintype A]{p:Sector A}{b c: Bool}
variable {K L:Flux A P R}{F H:Row A P R}{l r:Legs (Mode A P)}
abbrev Reverse (K:Flux A P R)(p:Sector A): Prop:= ∀ i j p', K i j (-p')=cross (p i) (p j)*K j i p'
-- single kern

def radius (p:Sector A) (K:Flux A P R)(i j:A)(F H:Row A P R) (l k: Legs (Mode A P)): R:=
    let q:= - net l; 2*K i j q*(cross (p j) (degree (field p) l)*F ((i,q)::l))* H ((j,-q)::k)
lemma convertR (he: Reverse K p) : attaches p K F H l r=∑ i,∑ j, radius p K i j F H l r:= by
    unfold attaches; simp_rw [sum_add_distrib]; conv_lhs=>arg 2; rw [Finset.sum_comm]; -- inner double sums
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i hi; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j hj; change K i j (-net l)*_ + K j i (- - net l)*_= _; rw [he j i (-net l)]; unfold radius; cases hx:p i <;> cases ht:p j <;> cases hu: degree (field p) l <;> simp <;> ring
-- moves.

def hits (p:Sector A)(K L:Flux A P R)(F H:Row A P R) (l r:Legs (Mode A P))(a e i j:A)(q:P): R:=
 L a e q * (cross (p e) (degree (field p) l) * radius p K i j F H ((a,q)::l) ((e,-q)::r))
def restL (p:Sector A)(K L:Flux A P R)(F H:Row A P R)(l r:Legs (Mode A P))(a e i j:A)(q:P): R:=
 L a e q * (cross (p a) (degree (field p) ((e,-q)::l)) * radius p K i j F H ((e,-q)::l) ((a,q)::r))
omit [Fintype A] in
lemma RL (h: Reverse L p)(a e i j:A)(q:P) : restL p K L F H l r a e i j (-q)=hits p K L F H l r e a i j q:= by
   unfold restL hits; simp only [neg_neg,h, field, degree_cons]; cases h0:p a <;> cases he:p e <;> cases hq:degree (field p) l <;> simp
-- x parity disjoint b,c
section
variable (he:b=false ∨ c=false)
include he
variable (h:closed K p b)(h':closed L p c)
include h h'
omit [Fintype A] [AddCommGroup P] in
lemma cross_budget {i j k t:A} {u v:P} (hk:K i j u ≠ 0)(hl:L k t v≠ 0): p i=p j ∨ p k=p t:= by
    rcases he with he|he; · left; symm; simpa [he] using h _ _ _ hk
    right; symm; simpa [he] using h' _ _ _ hl
omit [Fintype A] in
lemma dance_X (q:P)(a e i j:A)(hf:Symm (field p) F)(hg: Symm (field p) H): hits p K L F H l r a e i j q=hits p L K F H l r i j a e (- net l - q):= by
    unfold hits radius; simp only [degree_cons,field,net_cons]
    rw [show -(q+net l)= - net l-q by abel,show -(- net l-q + net l)=q by abel]
    by_cases hx:L a e q=0; simp [hx]; by_cases ht : K i j (-net l-q)=0; simp [ht]
    rw [show F ((i,-net l-q)::(a,q)::l)=cross (p i) (p a) * F ((a,q)::(i,-net l-q)::l) from hf [] (i,-net l-q) (a,q) l, show H ((j,- (-net l-q))::(e,-q)::r)=cross (p j) (p e)*H ((e,-q)::(j,-(-net l-q))::r) from hg [] (j,-(-net l-q)) (e,-q) r];
    rcases cross_budget he h h' ht hx with hh|hh
    · rw [hh]; cases a':p a <;> cases i':p j <;> cases e':p e <;> cases ht: degree (field p) l <;> simp <;> ring
    rw [hh]; cases a':p e <;> cases i':p i <;> cases e':p j <;> cases ht: degree (field p) l <;> simp <;> ring
-- loop pair inside left or right

omit [Fintype A] in
lemma LL (a e i j:A)(q:P)(hf:Symm (field p) F) : L a e q*radius p K i j F H ((a,q)::(e,-q)::l) r=
   radius p K i j (L a e q • diffPair (a,q) (e,-q) F) H l r:= by
    unfold radius; simp only [net_cons,degree_cons,field,diffPair_apply, at_D,Pi.smul_apply,smul_eq_mul, add_neg_cancel_left];
    by_cases h0: L a e q=0; simp [h0]; by_cases hP:K i j (-net l)=0; simp [hP]
    rw [show F ((i,-net l)::(a,q)::(e,-q)::l)=cross (p i) (p a)*F ((a,q)::(i,-net l)::(e,-q)::l) from hf [] (i,-net l) (a,q) ((e,-q)::l), show F ((a,q)::(i,-net l)::(e,-q)::l)=cross (p i) (p e)*F ((a,q)::(e,-q)::(i,-net l)::l) from hf [(a,q)] _ _ l];
    rcases cross_budget he h h' hP h0 with hi|ha
    · rw [hi]; cases h':p j <;> cases he:p a <;> cases hu:p e <;> cases degree (field p) l <;> simp <;> ring
    rw [ha]; cases h':p e <;> cases hu:p i <;> simp <;> ring
omit [Fintype A] in
lemma RR (a e i j:A)(q:P)(H':Symm (field p) H)(hs: Pure (field p) false F): L a e q*(cross (p e) (degree (field p) l) *(cross (p a) (degree (field p) l)* radius p K i j F H l ((a,q)::(e,-q)::r)))=
    radius p K i j F (L a e q • diffPair (a,q) (e,-q) H) l r:= by
   unfold radius; by_cases h0: L a e q=0; simp [h0]; by_cases hP:K i j (-net l)=0; simp [hP]
   simp only [diffPair_apply, Pi.smul_apply, at_D, smul_eq_mul]
   rw [show H ((j,- -net l)::(a,q)::(e,-q)::r)=cross (p j) (p a)*H ((a,q)::(j,- -net l)::(e,-q)::r) from H' [] (j,_) (a,q) ((e,-q)::r), show H ((a,q)::(j,- -net l)::(e,-q)::r)=cross (p j) (p e)*H ((a,q)::(e,-q)::(j,- -net l)::r) from H' [(a,q)] _ _ r];
   let t:=degree (field p) l; by_cases hI : p i = t; swap; · rw [hs ((i,- net l)::l) (by simpa [field] using hI)]; simp
   rcases cross_budget he h h' hP h0 with hi|ha
   · rw [hi] at hI; unfold t at hI; rw [← hI]; cases hp:p a <;> cases hp:p j <;> cases hL:p e <;> simp <;> ring -- same var
   rw [ha,show degree (field p) l=t from rfl]; cases hu:t <;> cases he:p e <;> cases h':p j <;> simp <;> ring
end
end YM.MS.Heat
