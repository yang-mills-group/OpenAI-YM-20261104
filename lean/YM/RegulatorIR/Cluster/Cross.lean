import YM.RegulatorIR.Diagram.Packed
import YM.RegulatorIR.Budget.Channels

/-! Product packets in the composite sources. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Finset MvPolynomial Function Budget Budget.Tuple Budget.Packet Diagram
open scoped Topology BigOperators Classical
variable {I J:Type}{a b r s:ℕ}

def untied (T:Packet I a) (S:Packet I b): Packet I (a+b):=fun z=> T (cutLeft z)*S (cutRight z)
def joined (T:Packet I a) (S:Packet I b): Packet I (a+b) := symmetry (untied T S)
lemma render_pair [Fintype I] (T:Packet I a)(S:Packet I b) : render (joined T S)=render T*render S:=by
 rw [joined,render_symmetry]; unfold render; rw [← (Fin.appendEquiv ..).sum_comp, Fintype.sum_prod_type,Finset.sum_mul]
 apply Finset.sum_congr rfl; intro x _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _
 change C (untied T S (Fin.append x y))*word (Fin.append x y)=_; simp only [untied,cutleft,cutright,map_mul]
 rw [show word (Fin.append x y)=word x *word y from ?_]; ring
 unfold word; rw [Fin.prod_univ_add]; simp

def pie (T S:Ranked I) (r:ℕ)(i: ℕ×ℕ): Packet I r:= if h:i.1+i.2=r then h ▸ joined (T i.1) (S i.2) else 0
def crisp (T S:Ranked I) : Ranked I := fun r=> ∑ i∈Finset.antidiagonal r,pie T S r i
lemma crop_pair (f:J↪I)(T:Packet I a)(S:Packet I b): crop f (joined T S)=joined (crop f T) (crop f S):=by
 ext1 z; change symmetry _ (acrossT f z)= symmetry _ z; rw [symmetry_at,symmetry_at]; rfl
lemma crop_sum {X:Type} (t:Finset X)(f:J↪I)(T:X→Packet I r) : crop f (∑ i∈t,T i) =∑ i∈t,crop f (T i):=by ext1 z; simp_rw [crop, Function.comp_apply,Finset.sum_apply]; rfl
lemma crop_crisp (f:J↪I)(T S:Ranked I) (a:ℕ) : crop f (crisp T S a) = crisp (fun r=>crop f (T r)) (fun r=>crop f (S r)) a:=by
 unfold crisp; rw [crop_sum]; apply Finset.sum_congr rfl; intro i hi
 have h:=Finset.mem_antidiagonal.mp hi
 rw [← h, pie,dif_pos rfl,pie,dif_pos rfl]; exact crop_pair ..
lemma pie_comes (T S:Ranked I)(a:ℕ) (i:ℕ×ℕ)(h:pie T S a i≠0): i.1+i.2=a ∧ T i.1 ≠ 0 ∧ S i.2≠0:=by
 unfold pie at h; split at h
 next hu=>
   subst a; refine ⟨rfl,fun h' => ?_,fun h'=>?_⟩
   · apply h; rw [h']; exact Eq.trans (congr_arg symmetry (show untied (0:Packet I _) (S _)=0 by ext1 z; simp [untied])) sym_zero
   apply h; rw [h']; exact Eq.trans (congr_arg symmetry (show untied (T _) (0:Packet I _)=0 by ext1 z; simp [untied])) sym_zero
 contradiction
lemma crisp_packed [Fintype I] (T S:Ranked I) (h:Within a T)(hh:Within b S) :
    packed (crisp T S) (a+b) = packed T a* packed S b:=by
 let f (i:ℕ×ℕ):= render (T i.1)*render (S i.2)
 have hp i : render (crisp T S i)=∑ j∈Finset.antidiagonal i,f j:=by
    rw [crisp,render_sum]; apply Finset.sum_congr rfl;intro j hj
    rw [← Finset.mem_antidiagonal.mp hj, pie,dif_pos rfl]; exact render_pair ..
 have ht : packed T a*packed S b=∑ i∈(Finset.range (a+1) ×ˢ Finset.range (b+1)),f i:=by simp only [f,Finset.sum_product,packed,Finset.sum_mul,Finset.mul_sum]; exact Finset.sum_comm
 rw [ht,packed]; simp_rw [hp]; rw [← Finset.sum_biUnion]; symm
 apply Finset.sum_subset
 · rintro ⟨x,y⟩ he
   simp only [Finset.mem_product, Finset.mem_range] at he; exact Finset.mem_biUnion.mpr ⟨x+y, Finset.mem_range.mpr (by omega),Finset.mem_antidiagonal.mpr rfl⟩
 · rintro ⟨x,y⟩ _ hx
   by_cases h':a<x
   · rw [show f (x,y)=_ from rfl]; unfold f; rw [show T x=0 from by by_contra! hm;exact not_lt.mpr (h x hm) h',render_zero,zero_mul]
   have hu : b<y:= by by_contra! hm; exact hx (by simp only [Finset.mem_product,Finset.mem_range]; omega)
   unfold f; rw [show S y=0 from by by_contra! hm; exact not_lt.mpr (hh y hm) hu, render_zero,mul_zero]
 intro i _ j _ hx; exact Finset.disjoint_left.mpr (fun x hi hj=> hx ((Finset.mem_antidiagonal.mp hi).symm.trans (Finset.mem_antidiagonal.mp hj)))

def accord (T U:Orders I) : Orders I:= fun i r=> ∑ p∈Finset.antidiagonal i,crisp (T p.1) (U p.2) r
lemma accord_order (T U:Orders I) (i:ℕ) : accord T U i=∑ p∈Finset.antidiagonal i, crisp (T p.1) (U p.2):=by ext1 r; rw [Finset.sum_apply]; rfl
lemma crop_orders (f:J↪I)(T U:Orders I)(i r:ℕ) : crop f (accord T U i r)= accord (fun i r=>crop f (T i r)) (fun i r=>crop f (U i r)) i r:= by simp only [accord,crop_sum,crop_crisp]
lemma adorns (T S:Ranked I) : Within r T → Within s S → Within (r+s) (crisp T S):=by
 intro h hh a hi
 obtain ⟨i,-,he⟩:= Finset.exists_ne_zero_of_sum_ne_zero hi
 obtain ⟨hx,hy,hp⟩:= pie_comes _ _ _ _ he; exact hx ▸ Nat.add_le_add (h _ hy) (hh _ hp)
lemma pie_sym (T U:Ranked I)(r p): IsSym (pie T U r p):=by
 unfold pie; split
 next he=>subst r; exact Packet.is_symmetry _
 exact Diagram.symmetric_zero
lemma crisp_sym (T U:Ranked I)(r:ℕ): IsSym (crisp T U r):= symmetric_sum fun _ _=> pie_sym _ _ _ _
lemma accord_sym (T U:Orders I): gradedSymmetric (accord T U):=fun _ _=> symmetric_sum fun _ _=>crisp_sym _ _ _
lemma accord_rank {T U:Orders I} (h:∀ e,Within (e+a) (T e)) (hh:∀ e,Within (e+b) (U e))(i:ℕ): Within (i+(a+b)) (accord T U i):=by
 intro r hr; obtain ⟨x,hx,he⟩:= Finset.exists_ne_zero_of_sum_ne_zero hr
 have h' := adorns _ _ (h x.1) (hh x.2) _ he
 have ht:= Finset.mem_antidiagonal.mp hx; omega

def composeT (T U:ℕ → Orders I) : ℕ→Orders I:= fun k e r=> ∑ p∈Finset.antidiagonal k,accord (T p.1) (U p.2) e r
lemma compose_order (T U:ℕ→Orders I)(k i:ℕ) : composeT T U k i=∑ p∈Finset.antidiagonal k,accord (T p.1) (U p.2) i:= by ext1 r; rw [Finset.sum_apply]; rfl
lemma crop_twice (f:J↪I)(T U: ℕ→Orders I)(k i r:ℕ) : crop f (composeT T U k i r)=composeT (fun k i r=>crop f (T k i r)) (fun k i r=>crop f (U k i r)) k i r:=by simp_rw [composeT,crop_sum,crop_orders]
lemma compose_sym (T U:ℕ→Orders I) (k:ℕ):gradedSymmetric (composeT T U k):=fun i j=> symmetric_sum (fun _ _=> accord_sym _ _ i j)
lemma compose_shape (T U:ℕ→Orders I)(h:∀ k i,Within (i+a) (T k i))(hh:∀ k i,Within (i+b) (U k i))(k i:ℕ):Within (i+(a+b)) (composeT T U k i):=by intro r hr; obtain ⟨p,_,hp⟩:= Finset.exists_ne_zero_of_sum_ne_zero hr; exact accord_rank (h p.1) (hh p.2) _ _ hp
end YM.RegulatorIR.Cluster
