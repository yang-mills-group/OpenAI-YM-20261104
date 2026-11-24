import YM.OPE.Compatible.Parch.Vine
import Mathlib.LinearAlgebra.Vandermonde
/-!
# Uniform Bills. Hessen mono for any support length.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Claw
open Function Filter Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {i j r d m k l:ℕ}
section
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
abbrev LimitR (C:ℝ)(f:E→F):= ∀ x,‖x‖≤1→ ‖f x‖ ≤ C
variable {f:E→F}
namespace Tall
lemma grades (h:Tall f k)(s:E)(t:ℝ): f (t • s)=∑ i: Fin (k+1), t^(i.val) • rank f i.val s:=by
        nth_rw 1 [h.allot]; rw [Finset.sum_apply,← Fin.sum_univ_eq_sum_range (fun i:ℕ=>rank f i (t • s))]; apply Finset.sum_congr rfl; exact fun _ _=> Tensor.homogeneous ..
-- even vector-valued and arity-uniform
local notation "I!"=>Fin (k+1)
def bars(k:ℕ)(i:Fin (k+1)):ℝ:= (i.val:ℝ)/((k:ℝ)+1)
lemma bars_inj (k:ℕ):Injective (bars k):= by intro i j h; apply Fin.ext; exact Nat.cast_injective (R:=ℝ) ((div_left_inj' (by positivity:((k:ℝ)+1)≠0)).1 h)
lemma barNorm (j:I!): ‖bars k j‖ ≤1:=by unfold bars; rw[Real.norm_of_nonneg (by positivity),div_le_one (by positivity)];exact_mod_cast (j.isLt.le)
lemma notate (n k:ℕ) (hp:n ≤ k): ∃ s:ℝ,0≤ s ∧ ∀ (E F:Type)[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](f:E→F) (_:Tall f k)(C:ℝ),LimitR C f→ LimitR (s*C) (rank f n):=by
       let P:= Matrix.vandermonde (bars k); let j:Fin (k+1):= ⟨n,by omega⟩; let D(l:Fin (k+1)):= P⁻¹ j l; have hv : P⁻¹*P=1:= Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr (bars_inj k)))
       have he(i:Fin (k+1)): ∑ t:Fin (k+1),D t* bars k t^i.val= if i=j then 1 else 0:=by rw[show (∑ t:Fin (k+1),D t* bars k t^i.val)= (P⁻¹*P) j i from rfl,hv]; by_cases h:i=j<;> simp[h,Matrix.one_apply]; exact Ne.symm h
       refine ⟨∑ i: Fin (k+1),‖D i‖,sum_nonneg (fun i _=>norm_nonneg _),fun E F _ _ _ _ f h C ht s hS=>?_⟩; have hg : rank f n s=∑ t:Fin (k+1), D t • f (bars k t • s):=by simp_rw [grades h]; simp_rw [Finset.smul_sum, smul_smul]; rw[Finset.sum_comm]; simp only [← Finset.sum_smul,he]; simp; rfl
       rw [hg,Finset.sum_mul]; apply (norm_sum_le ..).trans; refine sum_le_sum fun i _=>?_ ; rw[norm_smul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply ht; rw[norm_smul]; exact mul_le_one₀ (barNorm i) (norm_nonneg _) hS
end Tall
end
section Funds
variable {I:Type}{E F:I→Type} [∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)][∀ i,NormedAddCommGroup (F i)][∀ i,NormedSpace ℝ (F i)]
noncomputable def Bills (φ:Filter I)(Z:I→ℝ) (p:(i:I)→E i→F i):Prop:=∃ v:I→ℝ, RateLE φ Z v 0∧∀ᶠ i in φ,LimitR (v i) (p i)
variable {φ:Filter I}{Γ:I→ℝ} (ht:Tendsto Γ φ atTop){p q:(i:I)→E i→F i}
namespace Bills
omit [(i : I) → NormedSpace ℝ (E i)] [(i : I) → NormedSpace ℝ (F i)] in lemma merge (h:Bills φ Γ p)(h':∀ᶠ i in φ,p i=q i):Bills φ Γ q:=by obtain ⟨c,hc,H⟩:=h; exact ⟨c,hc,(H.and h').mono fun i hi=> hi.2 ▸ hi.1⟩ -- EventuallyEq dependent doesn't work!
include ht
omit [(i : I) → NormedSpace ℝ (E i)] [(i : I) → NormedSpace ℝ (F i)] in lemma bite (h:Bills φ Γ p)(hv:Bills φ Γ q):Bills φ Γ (p-q):=by obtain ⟨c,hc,H⟩:=h; obtain ⟨v',hv,hV⟩:=hv; exact ⟨_,hc.add hv ht,(H.and hV).mono fun i hi x h=>(norm_sub_le ..).trans (add_le_add (hi.1 x h) (hi.2 x h))⟩
omit [(i : I) → NormedSpace ℝ (E i)] [(i : I) → NormedSpace ℝ (F i)] in lemma zeroB:Bills φ Γ (0:(i:I)→E i→F i):=⟨fun _=>0,RateLE.const _ ht,Eventually.of_forall (fun i _ _=>(norm_zero (E:=F i)).le )⟩
omit [(i : I) → NormedSpace ℝ (E i)] [(i : I) → NormedSpace ℝ (F i)] in lemma add (h:Bills φ Γ p)(hv:Bills φ Γ q):Bills φ Γ (p+q):= by rw [show p+q=p-(0-q) from by simp]; exact bite ht h (bite ht (zeroB ht) hv)
omit [(i : I) → NormedSpace ℝ (E i)] [(i : I) → NormedSpace ℝ (F i)] in lemma sum {J:Type}(P:J→(i:I)→E i→F i)(k: Finset J)(h:∀ i∈k,Bills φ Γ (P i)): Bills φ Γ (∑ i∈k,P i):=by
       induction k using Finset.induction_on with
       | empty=> rw [sum_empty];exact zeroB ht
       | insert i s hi ih=> rw [sum_insert hi];exact Bills.add ht (h _ (mem_insert_self ..)) (ih (fun i hi=>h _ (mem_insert_of_mem hi)))
lemma rankFee (h:Bills φ Γ p)(he:∀ᶠ i in φ,Tall (p i) d)(hk:k ≤ d): Bills φ Γ (fun i=>rank (p i) k):=by
        obtain ⟨c,hc,H⟩:=Tall.notate k d hk; obtain ⟨b,hb,h⟩:=h; exact ⟨_,((RateLE.const c ht).mul hb).mono (by norm_num),(he.and h).mono fun i hi=>H _ _ _ hi.1 _ hi.2⟩
-- every Budget(v) ball vouchers. Also require all pμ.R shape. 
lemma radiusH {V:I→ℝ}(hV:RateLE φ Γ V 0)(h:Bills φ Γ p)(he:∀ᶠ i in φ,Tall (p i) d) :∃ c:I→ℝ,RateLE φ Γ c 0∧∀ᶠ i in φ,∀ x:E i,‖x‖≤ V i→‖p i x‖≤ c i:=by
        let J:=range (d+1); choose! b hb H using fun i (hi:i∈J)=>rankFee ht h he (show i≤d from by have hx:= mem_range.mp hi; omega); let f(i):= ‖V i‖+1
        have hf(i):0<f i:=add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one; let q(j i):= f i^j * b j i; have hx(j:ℕ)(hh:j∈J): RateLE φ Γ (q j) 0:= ((((hV.norm.add (RateLE.const 1 ht) ht).pow j ht)).mul (hb j hh)).mono (by norm_num)
        refine ⟨_, RateLE.sum ht hx,?_⟩; filter_upwards [he,eventually_all_finset J|>.2 H] with i hi hv x he; nth_rw 1 [hi.allot]; rw [Finset.sum_apply]; refine (norm_sum_le ..).trans (sum_le_sum fun j hj=>?_); let z: E i:= (f i)⁻¹ • x; have hZ:‖z‖ ≤ 1:=by unfold z; rw [norm_smul,norm_inv,Real.norm_of_nonneg (hf i).le]; exact (mul_le_mul_of_nonneg_left (he.trans ((Real.le_norm_self _).trans (le_add_of_nonneg_right zero_le_one))) (inv_nonneg.mpr (hf i).le)).trans_eq (inv_mul_cancel₀ (hf i).ne')
        have hT:f i • z=x:=smul_inv_smul₀ (hf i).ne' x; rw [←hT,rank,Tensor.homogeneous,norm_smul,norm_pow,Real.norm_of_nonneg (hf i).le]; exact mul_le_mul_of_nonneg_left (hv _ hj z hZ) (pow_nonneg (hf _).le _)
end Bills
end Funds
end YM.OPE.Claw
