import YM.XSpace.Sparks
import YM.XSpace.Reservoir

/-!
# The double-null-residue calculation for the stabilizer

At each step only one middle vertex goes complex. Equality for REAL separated
correlations suffices, even though this step cannot be done with simultaneous
real-point collisions. Easy connectivity tests: because the weight-four block
is fixed, both legs to a-single-endpoint graph vanishes separately in the variation!
Thus we can use both poles at ONCE in only one univariate interpolation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Legs
open Traverse Function Set Filter Finsupp Maxwell Maxwell.Free
open MvPolynomial Next.Rank.Normal
open scoped Topology BigOperators Classical
variable {G : Gauge} {S : Finset E4} {v u c x y : E4}

variable (s : Flavor 0) (H : Wheel v u) (C₀ a : G.ColorIndex)

def swell (v u c : E4) (t : ℝ): World G→ ℂ:= timer v u t • ((Kf G).cov (lit (course c u t) s a))
include H in
lemma quiet_swell (w : World G) (h : jump (interval (c-w.1) u) ≠ 0) : Landing (fun t=> swell s a v u c t w) 0:=by
  obtain ⟨z,hz⟩:= travels (dot s a) w.2 (v:=c-w.1) H.runs h
  simpa only [zero_mul] using (((zero_timer H).mul hz).congr (g:=fun t=> swell s a v u c t w) (by
    filter_upwards [rolling H c w.1] with t ht; unfold swell; rw [Pi.smul_apply,smul_eq_mul,cash _ _ ht]; congr 2
    rw [show (lit (course c u t) s a).1-w.1=course (c-w.1) u t from ?_]; rfl
    unfold lit course; dsimp only; abel))
lemma hot_swell (p : Flavor 0) (c : E4) (b : G.ColorIndex) : Landing (fun t=> swell s a v u c t (lit (c-v) p b)) (if a=b then flash H C₀ s p else 0) := by
  by_cases h:a=b
  · rw [if_pos h]; apply (flashed H C₀ s p).congr; filter_upwards [rolling H c (c-v)] with t ht
    unfold swell; let z:= course c u t; rw [Pi.smul_apply,smul_eq_mul,lit,lit,dot,dot,colors C₀ ht,if_pos h,show z-(c-v)=course v u t from ?_]
    unfold z course; abel
  rw [if_neg h]; apply (constant _).congr; filter_upwards [rolling H c (c-v)] with t ht
  unfold swell; rw [Pi.smul_apply,smul_eq_mul,lit,lit,dot,dot,colors C₀ ht,if_neg h, mul_zero]

def Lhot (x y : E4) (p q : Flavor 0) (A B : ℂ) (e : G.ColorIndex) := choose_var (lit x p e) A + choose_var (lit y q e) B
lemma L_on (hw : x≠y) (e f : G.ColorIndex) (p q : Flavor 0) (A B :ℂ):
    Lhot x y p q A B e (lit x p f)=(if e=f then A else 0) := by
  simp only [Lhot,Pi.add_apply]; rw [chosen_ne (show lit x p f≠lit y q e from fun h=> hw (congr_arg Prod.fst h)),add_zero]
  split_ifs with h; rw [h,chosen_eq]; exact chosen_ne (fun z=>h (congr_arg (fun k : World G=> k.2.2) z).symm) _
lemma L_flip (x y : E4) (e : G.ColorIndex) (p q : Flavor 0) (A B : ℂ): Lhot x y p q A B e=Lhot y x q p B A e:= add_comm ..
lemma L_other (hw : forall y:E4, y∈S → y≠x) (hy : ∀ z:E4,z∈S→ z≠y) (e:G.ColorIndex) {w : World G} (hh : w.1∈S) (p q : Flavor 0) (A B :ℂ): Lhot x y p q A B e w=0:=by
  unfold Lhot; rw [Pi.add_apply, chosen_ne (show w≠lit x p e from fun h=> hw _ hh (congr_arg Prod.fst h)),chosen_ne (show w≠lit y q e from fun h=> hy _ hh (congr_arg Prod.fst h)), add_zero]

-- Double term
section slits
variable (p q : Flavor 0) (A B : ℂ) (hw : x≠y)
include hw
lemma twice_one : slit (Lhot x y p q A B a) (bilocal G (x,p) (x,p))= C (2*A)* X (lit x p a):=by
  unfold bilocal; rw [_root_.map_sum, Finset.sum_eq_single a]; swap
  · intro i _ ht; rw [split_leibniz]; simp only [slit_X, L_on hw, if_neg ht.symm, map_zero,mul_zero,zero_mul,zero_add]
  rw [split_leibniz]; simp only [slit_X,L_on hw, if_true]; rw [two_mul,map_add]; ring
  simp

omit hw in
lemma dollar (Q R : Pol G) (c : ℂ): receive G (C c*(Q*R))=c*receive G (Q*R):=by rw [C_mul', map_smul]; rfl

lemma double_pays (P : Pol G) (hp : slit (Lhot x y p q A B a) P=0) (he : receive G (bilocal G (x,p) (x,p)*P)=0)
    (ht : receive G (bilocal G (y,q) (y,q)*P)=0): receive G (slit (Lhot x y p q A B a) (slit (Lhot x y p q A B a) (bilocal G (x,p) (x,p)*(bilocal G (y,q) (y,q)*P))))=8*A*B*receive G (X (lit x p a) *X (lit y q a)*P):=by
  let D:= slit (Lhot x y p q A B a); let U:=X (R:=ℂ) (lit x p a); let V:= X (R:=ℂ) (lit y q a); let x':=bilocal G (x,p) (x,p); let y':=bilocal G (y,q) (y,q)
  have hu : D U=C A:= by unfold D U; rw [slit_X,L_on hw,if_pos rfl]
  have hv : D V=C B:= by unfold D V; rw [slit_X,L_flip,L_on (Ne.symm hw),if_pos rfl]
  have hf : D x'=C (2*A)*U:=twice_one a p q A B hw
  have hg : D y'=C (2*B)*V:=by unfold D; rw [L_flip]; exact twice_one a q p B A (Ne.symm hw)
  have h: receive G (D (D (x'*(y'*P))))= receive G ((C (2*A*A)*(y'*P) + C (2*B*B)*(x'*P))+ C (8*A*B)*(U*V*P)):=by
    apply congr_arg; unfold D at hu hv hf hg ⊢
    simp only [split_leibniz,hp,hf,hg,hu,hv,mul_zero, add_zero,_root_.map_add,slit_C]; simp only [map_mul,map_ofNat]; ring
  change receive G (D (D (x'*(y'*P))))=_; rw [h,map_add,map_add,dollar,dollar,dollar,ht,he,mul_zero,mul_zero,zero_add,zero_add]
end slits

include H in
lemma collide (P : Pol G) (x y : Ph) (hx : x.1=c-v) (hy : y.1=c+v) (hz : x.1≠y.1)
    (hp : P ∈ Room G S) (he : x.1∉S) (ht : y.1∉S) (hU : ∀ z∈S, jump (interval (c-z) u) ≠ 0) (ha : receive G (bilocal G x x * P)=0)
    (hb : receive G (bilocal G y y * P)=0) : Landing
      (fun t=> timer v u t ^2*receive G ((post (course c u t) (quad s))*(bilocal G x x*(bilocal G y y*P))))
      (8*flash H C₀ s x.2*flash H.back C₀ s y.2*receive G (bilocal G x y*P)):=by
  let K:=Kf G; let Q:=bilocal G x x*(bilocal G y y*P); let A:=flash H C₀ s x.2; let B:=flash H.back C₀ s y.2
  let U : Set (World G) := {w | w.1 ∈ S} ∪ Set.range (lit x.1 x.2) ∪ Set.range (lit y.1 y.2)
  have hQ : Q ∈ supported ℂ U:=by
    have hk (x : Ph) (hi : Set.range (lit x.1 x.2 (G:=G))⊆U): bilocal G x x∈ supported ℂ U:= Subalgebra.sum_mem _ fun _ _=> Subalgebra.mul_mem _ (X_mem_supported.mpr (hi ⟨_,rfl⟩)) (X_mem_supported.mpr (hi ⟨_,rfl⟩))
    exact Subalgebra.mul_mem _ (hk x (subset_union_right.trans subset_union_left)) (Subalgebra.mul_mem _ (hk y subset_union_right) ((show Room G S ≤ supported ℂ U from supported_mono fun _ ht=> Or.inl (Or.inl ht)) hp))
  let f (a:G.ColorIndex):= Lhot x.1 y.1 x.2 y.2 A B a
  let g (a:G.ColorIndex):= swell s a v u c
  have hL (a:G.ColorIndex) (w : World G) (hw : w.1∈S) : f a w=0:= L_other (x:=x.1) (y:=y.1) (fun z hz ht=> he (ht ▸ hz)) (fun z hz h=> ht (h ▸ hz)) _ hw ..
  have hK (a:G.ColorIndex) (w : World G) (hw : w∈U): Landing (fun t=> g a t w) (f a w):= by
    rcases hw with (hw | ⟨i,rfl⟩) | ⟨i,rfl⟩
    · rw [hL a _ hw]; exact quiet_swell s H a w (hU _ hw)
    · unfold f; rw [L_on hz]; exact hx.symm ▸ hot_swell s H C₀ a x.2 c i
    unfold f; rw [L_flip,L_on (Ne.symm hz)]; have hh:= hot_swell s H.back C₀ a y.2 c i; rw [sub_neg_eq_add,← hy] at hh
    unfold swell at hh; rw [timer_back H] at hh; exact hh
  let z (t : ℝ) := (course c u t,s)
  let W (a:G.ColorIndex) (t : ℝ) := lit (z t).1 s a
  let Gp (a:G.ColorIndex):= slit (f a) (slit (f a) Q)
  have hx (a:G.ColorIndex): slit (f a) P=0:= by rw [split_eq (f a) 0 (fun w hw=> hL a w hw) (show P∈supported ℂ (Prod.fst ⁻¹' (S:Set E4)) from hp),slit_zero]
  have hm : Landing (fun t => ∑ a:G.ColorIndex, receive G (slit (g a t) (slit (g a t) Q))) (∑ a:G.ColorIndex, receive G (Gp a)):= by
    refine landed_sum _ _ _ fun a _=>?_ ; let Z:= fun t=> slit (g a t);
    exact varied_splits (f a) (g a) (hK a) hQ (fun t=> (receive G).comp (Z t).toLinearMap) ((receive G).comp (slit (f a)).toLinearMap) (fun P h=> varied_splits (f a) (g a) (hK a) h (fun _=>receive G) _ fun Q _=> Traverse.constant _)
  have hr a t : receive G (X (W a t)*X (W a t)*Q)=receive G (slit (K.cov (W a t)) (slit (K.cov (W a t)) Q)) :=by
    rw [mul_assoc]; unfold receive; rw [stationed]; change Next.Rank.Normal.blend K 0 (slit (K.cov (W a t)) _) = _; rw [slit_prod, show K.cov (W a t) (W a t)=0 from empty_self .., map_zero,zero_mul,add_zero,stationed]
  have hh (a:G.ColorIndex) : receive G (Gp a)=8*A*B*receive G (X (lit x.1 x.2 a)*X (lit y.1 y.2 a)*P) := double_pays _ _ _ _ _ hz _ (hx a) ha hb
  simp_rw [hh] at hm
  have hf a t : slit (g a t) (slit (g a t) Q)= (timer v u t)^2 • slit (K.cov (W a t)) (slit (K.cov (W a t)) Q):=by
    rw [show g a t=timer v u t • K.cov (W a t) from rfl, slit_smul, slit_smul, (slit _).map_smul, smul_smul,pow_two]
  rw [show receive G (bilocal G x y *P)=∑ a:G.ColorIndex, receive G (X (lit x.1 x.2 a)*X (lit y.1 y.2 a)*P) from by rw [bilocal,Finset.sum_mul,map_sum],Finset.mul_sum]
  apply hm.congr; filter_upwards with t; rw [quad_play]; unfold bilocal; rw [Finset.sum_mul,map_sum,Finset.mul_sum];
  refine Finset.sum_congr rfl fun a _=>?_ ; rw [hf,map_smul,← hr]; rfl
end YM.XSpace.Legs
