import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Mutual
/-!
# Odd-odd switching, for BV cohomology with real-momentum (non-torus) loops
Use the ACTUAL `tree` (with evaluation on the momentum hyperplane on LEFT input),
so interchanging the lines also changes the integration variable. Parallel to Heat.Quad.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Ward
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat
variable {R A P : Type} [AddCommGroup P] [CommRing R]{p:Sector A}
variable {K L:Flux A P R}{F H:Row A P R}{l r:Legs (Mode A P)}
variable (h:closed K p true)(h':closed L p true)
include h h'
lemma dance (q:P)(a e i j:A)(hf:MS.Koszul.Symm (field p) F)(hg: MS.Koszul.Symm (field p) H):
    hits p K L F H l r a e i j q= - hits p L K F H l r i j a e (- net l - q):= by
    unfold hits radius; simp only [degree_cons,field,net_cons]
    rw [show -(q+net l)= - net l-q by abel,show -(- net l-q + net l)=q by abel]
    by_cases hx:L a e q=0; simp [hx]; by_cases ht : K i j (-net l-q)=0; simp [ht]
    rw [show F ((i,-net l-q)::(a,q)::l)=cross (p i) (p a) * F ((a,q)::(i,-net l-q)::l) from hf [] (i,-net l-q) (a,q) l, show H ((j,- (-net l-q))::(e,-q)::r)=cross (p j) (p e)*H ((e,-q)::(j,-(-net l-q))::r) from hg [] (j,-(-net l-q)) (e,-q) r]
    have h0:= h _ _ _ ht; have h1:= h' _ _ _ hx
    cases a':p a <;> cases i':p i <;> cases e':p e <;> cases j':p j <;> simp [a',i',e',j'] at h0 h1
    all_goals cases hd: degree (field p) l <;> simp <;> ring
lemma left (a e i j:A)(q:P)(hf:MS.Koszul.Symm (field p) F) : L a e q*radius p K i j F H ((a,q)::(e,-q)::l) r=
   - radius p K i j (L a e q • diffPair (a,q) (e,-q) F) H l r:= by
    unfold radius; simp only [net_cons,degree_cons,field,diffPair_apply, at_D,Pi.smul_apply,smul_eq_mul, add_neg_cancel_left]
    by_cases h0: L a e q=0; simp [h0]; by_cases hP:K i j (-net l)=0; simp [hP]
    rw [show F ((i,-net l)::(a,q)::(e,-q)::l)=cross (p i) (p a)*F ((a,q)::(i,-net l)::(e,-q)::l) from hf [] (i,-net l) (a,q) ((e,-q)::l), show F ((a,q)::(i,-net l)::(e,-q)::l)=cross (p i) (p e)*F ((a,q)::(e,-q)::(i,-net l)::l) from hf [(a,q)] _ _ l]
    have ht:= h _ _ _ hP; have hk:= h' _ _ _ h0
    cases a':p a <;> cases i':p i <;> cases e':p e <;> cases j':p j <;> simp [a',i',e',j'] at ht hk
    all_goals cases hd: degree (field p) l <;> simp <;> ring
lemma right (a e i j:A)(q:P)(hg:MS.Koszul.Symm (field p) H)(hs: Pure (field p) false F): L a e q*(cross (p e) (degree (field p) l) *(cross (p a) (degree (field p) l)* radius p K i j F H l ((a,q)::(e,-q)::r)))=
    - radius p K i j F (L a e q • diffPair (a,q) (e,-q) H) l r:= by
   unfold radius; by_cases h0: L a e q=0; simp [h0]; by_cases hP:K i j (-net l)=0; simp [hP]
   simp only [diffPair_apply, Pi.smul_apply, at_D, smul_eq_mul]
   rw [show H ((j,- -net l)::(a,q)::(e,-q)::r)=cross (p j) (p a)*H ((a,q)::(j,- -net l)::(e,-q)::r) from hg [] (j,_) (a,q) ((e,-q)::r), show H ((a,q)::(j,- -net l)::(e,-q)::r)=cross (p j) (p e)*H ((a,q)::(e,-q)::(j,- -net l)::r) from hg [(a,q)] _ _ r]
   by_cases hI : p i = degree (field p) l
   swap; · rw [hs ((i,- net l)::l) (by simpa [field] using hI)]; simp
   have ht:= h _ _ _ hP; have hk:= h' _ _ _ h0
   rw [← hI]; cases a':p a <;> cases i':p i <;> cases e':p e <;> cases j':p j <;> simp [a',i',e',j'] at ht hk
   all_goals simp; ring
-- anti target signs p output parity.Scope
end YM.FVA2.O.Ward
