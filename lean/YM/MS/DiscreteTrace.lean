import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import YM.MS.Plane

/-! # From pair contraction to the momentum-local calculus (prior discrete version)

Unnormalized trace loop. In `tree` connections a bulk density exactly kills line
sum. This allows measure approximations with large normalization on bulk vertices in
proving continuum identities. The ambient group can also be infinite: just require
line vanish off the sampling support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane.Flux
open Function Set Finset Koszul
variable {A P R I : Type*} [AddCommGroup P] [CommRing R] [Fintype A] {p : Sector A} {b : Bool}
   {K : Flux A P R} {F H : Row A P R}

def slab (K : Flux A P R) (s : Finset P) : Op (Mode A P) R := ∑ q ∈ s, trc K q

lemma is_loop (s : Finset P) : slab K s = loop (fun (i:P×A×A)=> K i.2.1 i.2.2 i.1) (fun i=> (i.2.1,i.1)) (fun i=>(i.2.2,-i.1)) (s×ˢ ((Finset.univ : Finset A)×ˢ(Finset.univ : Finset A))) := by simp only [slab,loop,trc, sum_product]
lemma closed.balanced (h : closed K p b) (s : Finset P) : Balanced (field p) b (fun (i:P×A×A)=> K i.2.1 i.2.2 i.1) (fun i=> (i.2.1,i.1)) (fun i=>(i.2.2,-i.1)) (s×ˢ ((Finset.univ : Finset A)×ˢ(Finset.univ : Finset A))) := fun _ _ hk=> h _ _ _ hk
lemma closed.pure {c : Bool} (h : closed K p b) (s : Finset P) (hf : Koszul.Pure (field p) c F) : Koszul.Pure (field p) (c ^^ b) (slab K s F):= by rw [is_loop]; exact (h.balanced s).pure hf
lemma slab_conserved (s : Finset P) (h : Conserved F) : Conserved (slab K s F) := by
   intro w hw; simp only [slab,LinearMap.sum_apply, Finset.sum_apply]; exact sum_eq_zero fun i _=> conserved_trc _ i h w hw
lemma slab_sym (s : Finset P) (hf : Symm (field p) F) : Symm (field p) (slab K s F):= by rw [is_loop]; exact loop_symm hf
omit [Fintype A] in
lemma split_line (a e : A) (p : Sector A) (q:P) (h : (p e ^^ p a)=b) (K H: Row A P R) (w) :
    link (diffPair (a,q) (e,-q)) b (field p) K H w =
     scatter (field p) w (fun l r=> ((cross (p e) (degree (field p) l) * K ((a,q)::l))*H ((e,-q)::r))+
                        ((cross (p a) ((p e).xor (degree (field p) l)) * K ((e,-q)::l))*H ((a,q)::r))) := by
     rw [link_pair (a,q) (e,-q) (p:=field p) h,Pi.add_apply,scattered,scattered]; change allocate _ w _ + allocate _ w _= allocate _ w _; rw [← map_add]; congr!
omit [AddCommGroup P] in
private lemma regain {j : P} (s : Finset P) {f : P→R} (h : ∀ i≠j, f i=0) (ht : j∉s→ f j=0) :
    ∑ i∈s, f i=f j:= Finset.sum_eq_single j (fun i _=> h i) ht

lemma localize (h : closed K p b) (s : Finset P) (hs : ∀ q∉s, ∀ i j, K i j q=0) (hP : Conserved F) (G : Row A P R) : link (slab K s) b (field p) F G = tree p K F G := by
   classical
   ext w
   let U a e (q:P) (l r:Legs (Mode A P)):= K a e q * ((cross (p e) (degree (field p) l)*F ((a,q)::l))*G ((e,-q)::r))
   let V a e (q:P) (l r:Legs (Mode A P)):= K a e q * ((cross (p a) ((p e).xor (degree (field p) l))*F ((e,-q)::l))*G ((a,q)::r))
   have hu (i k:A) (q:P) : (K i k q • link (diffPair (i,q) (k,-q)) b (field p) F G) w = allocate (field p) w (U i k q+ V i k q) := by
       by_cases hs:K i k q=0
       · have hh: U i k q+ V i k q=0:= by ext; simp [U,V,hs]
         rw [hs, hh,map_zero]; simp
       rw [Pi.smul_apply,split_line _ _ _ _ (h _ _ _ hs)]; change _ • (allocate (field p) w _) = _; rw [← map_smul]; congr! 1; ext; simp [U,V, mul_add]
   simp only [slab, trc, link_sum, link_scale, Finset.sum_apply]
   change _ = allocate _ w (attaches p K F G); simp_rw [hu]; rw [sum_comm (s:=s)]; -- inspect
   simp_rw [sum_comm (s:=s), ← map_sum]; apply congr_arg; ext l r; simp only [Finset.sum_apply, Pi.add_apply, Finset.sum_add_distrib, attaches]
   refine congr_arg₂ _ (sum_congr rfl fun i _=> sum_congr rfl fun j _=> ?_) (sum_congr rfl fun i _=> sum_congr rfl fun j _=> ?_) -- adjusts
   · refine Eq.trans (regain (j:=-net l) s (fun q hq=>?_) (fun hs'=>?_)) rfl
     · unfold U; rw [hP ((i,q)::l) (by simpa [← eq_neg_iff_add_eq_zero] using hq), mul_zero,zero_mul,mul_zero]
     simp [U,hs _ hs']
   · refine Eq.trans (regain (j:= - - net l) s (fun q hq=> ?_) (fun hs'=>?_)) (by simp [V])
     · have hh: net ((j,-q)::l)≠0:= by rw [net_cons]; simp only; intro h; apply hq; simp [neg_add_eq_zero.mp h]
       simp only [V,hP _ hh,mul_zero,zero_mul]
     simp only [V,hs _ hs',zero_mul]
end YM.MS.Plane.Flux
