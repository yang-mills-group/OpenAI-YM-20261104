import YM.MatchingLedger.Mountain.Peak
import Mathlib.Analysis.Calculus.SmoothSeries


/-! # Occurrence-wise budget here uses *true path length* (not displacement); use
 Support.T for hierarchical interpretation ONLY after paying more. Every orientation independent.
 `Bonds` at actual height. E of the candidates (coming later) has SEPARATE `Budget` and
 lives in different spaces; even if same valuation, leave masks etc alone. This profile will ask
 also a probe on those entries on the given support/sup ledger.

 History aperture sets all real Cone sites. No continuity assertion of sums in larger Banach
 norms here except the explicit norm derivatives; fixed-volume identity domain.
 -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.MatchingLedger.Mountain
open Set Function Filter Precision RG MeasureTheory Lattice Wilson Metric Tensor Push.Uniform
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius Classical
variable {ι κ E F G : Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
   [NormedAddCommGroup F] [NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G]
   {Z C M r μ:ℝ} {f:ι→ E→ F} {g:κ→E→F}
   {d:ι→ℕ}{l:κ→ℕ}{k N:ℕ}

/-- fixed order seminorms. Screen transforms *anywhere in aperture*. -/
def revenue (r:ℝ)(n:ℕ)(μ:ℝ)(d:ι→ℕ)(f:ι→ E→ F)(Z:ℝ) := ∃ b:ι→ℝ,(∀ i, 0≤b i)∧ SumBudget (fun i=> Real.exp (μ*d i) * b i) Z ∧∀ i u, u∈ball 0 r→ Allows n (f i) u (b i)

namespace revenue
variable (h : revenue r N μ d f C) (he:0<r) (hm:0≤μ)
def book (_h : revenue r N μ d f C) : ι→ℝ:= _h.choose
include h
lemma budget : SumBudget (fun i=>Real.exp (μ*d i)*h.book i) C:=h.choose_spec.2.1
lemma straight (i:ι): 0 ≤ h.book i := h.choose_spec.1 i
lemma proceeds (i:ι)(u:E)(hx:u∈ball 0 r): Allows N (f i) u (h.book i):= h.choose_spec.2.2 i u hx
lemma burden : 0≤ C:= (tsum_nonneg h.budget.1).trans h.budget.2.2
lemma pair (hv:revenue r N μ l g M): revenue r N μ (Sum.elim d l) (Sum.elim f g) (C+M):=by
   let A:=fun s:ι⊕κ=>Real.exp (μ*Sum.elim d l s)*Sum.elim h.book hv.book s -- edit
   have hA (v:ι⊕κ): 0≤Sum.elim h.book hv.book v:= Sum.rec (motive:=fun v=>0≤Sum.elim h.book hv.book v) h.straight hv.straight v
   have hf:Summable (A ∘ Sum.inl):= h.budget.2.1; have hg:Summable (A ∘ Sum.inr):= hv.budget.2.1
   refine ⟨Sum.elim h.book hv.book,hA,⟨fun v=>mul_nonneg (Real.exp_pos _).le (hA v),hf.sum _ hg, ?_⟩,fun v u hx=>?_⟩
   · change ∑' i,A i ≤ _; rw [Summable.tsum_sum (f:=A) hf hg]; exact add_le_add h.budget.2.2 hv.budget.2.2
   cases v with
   | inl i=> exact h.proceeds i _ hx
   | inr i=> exact hv.proceeds i _ hx
omit h in
lemma staple [Fintype κ] {u : κ → ι → E → F} {A:κ→ι→ℕ}{P:κ→ℝ}
     (hv : ∀ i, revenue r N μ (A i) (u i) (P i)): revenue r N μ (uncurry A) (uncurry u) (∑ i,P i):=by
  let f i := (hv i).book
  let g i:=fun k:ι=> Real.exp (μ*A i k)*f i k
  have ht : Summable (uncurry g):= (summable_prod_of_nonneg (fun i=> (hv i.1).budget.1 _)).2 ⟨fun i=> (hv i).budget.2.1,(hasSum_fintype _).summable⟩
  refine ⟨uncurry f,fun i=>(hv i.1).straight _,⟨fun i=>(hv i.1).budget.1 _,ht,?_⟩,fun i=> (hv i.1).proceeds i.2⟩
  change ∑' i,uncurry g i ≤ _; rw [ht.tsum_prod,tsum_fintype]; exact Finset.sum_le_sum fun i _=> (hv i).budget.2.2

lemma limited (M:ℝ)(hm:C≤M) : revenue r N μ d f M:= ⟨_,h.straight,⟨h.budget.1, h.budget.2.1, h.budget.2.2.trans hm⟩, h.proceeds⟩
lemma inflate (s:ℝ): revenue r N μ d (fun i=> s • f i) (|s| *C):= by
  let f' : ι→ℝ:= fun i=> |s| *h.book i
  let b:=fun i=> Real.exp (μ*d i)* h.book i
  refine ⟨f',fun i=>mul_nonneg (abs_nonneg _) (h.straight i),?_,fun i u hx=>(h.proceeds i u hx).smul _⟩
  have he: (fun i=> Real.exp (μ*d i)* f' i)=(fun i=> |s| *b i):= funext fun i=> mul_left_comm _ _ _
  rw [he]; exact ⟨fun i=> mul_nonneg (abs_nonneg _) (h.budget.1 i),h.budget.2.1.mul_left _,by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.budget.2.2 (abs_nonneg _)⟩

section fall
variable {f:ι→ E→ F} (H:revenue 1 (k+1) μ d f C)
include H
omit h
lemma profiled {s:ℝ} (hr:1≤r)(he:0<s)(hv:s*r<1) (hk:N≤k+1) : revenue r N μ d (fun i=>bit (f i) k s) (C * r^(k+1) * s^(k+1)):=by
   let u:= r^(k+1)* s^(k+1); let b : ι→ℝ:=fun i=> H.book i * u; have hu:0≤ u:=by unfold u; positivity
   let f' : ι→ℝ:=fun i=> Real.exp (μ*d i)*H.book i; have hx : (fun i=>Real.exp (μ*d i)*b i)=fun i=>f' i*u:=funext fun i=> (mul_assoc ..).symm
   refine ⟨b,fun i=>mul_nonneg (H.straight i) hu,⟨fun i=>mul_nonneg (Real.exp_pos _).le (mul_nonneg (H.straight i) hu), hx.symm ▸ (H.budget.2.1.mul_right u),?_⟩,fun i x hi=> ?_⟩
   · rw [hx,tsum_mul_right]; exact (mul_le_mul_of_nonneg_right H.budget.2.2 hu).trans_eq (mul_assoc ..).symm
   exact (show _=b i from mul_assoc (H.book i) (r^(k+1)) (s^(k+1))) ▸ (rarity (f i) hr he hv (H.proceeds i) x (mem_ball_zero_iff.mp hi).le hk)
end fall
include hm h
lemma cash : SumBudget h.book C:=by
   have he i : h.book i ≤ Real.exp (μ*d i)*h.book i:= le_mul_of_one_le_left (h.straight i) (Real.one_le_exp (by positivity))
   have hp := h.budget.2.1.of_nonneg_of_le h.straight he
   exact ⟨h.straight,hp,(hp.tsum_le_tsum he h.budget.2.1).trans h.budget.2.2⟩
variable [CompleteSpace F]
lemma values {v:E}(hx:v∈ball 0 r): Summable (fun i=>f i v):= .of_norm_bounded (h.cash hm).2.1 (fun i=>(h.proceeds i v hx).value)
lemma reads {v:E}(hx:v∈ball 0 r)(hk:k≤N): Summable (fun i=>iteratedFDeriv ℝ k (f i) v):= .of_norm_bounded (h.cash hm).2.1 (fun i=>(h.proceeds i v hx).norm_le k hk)
lemma ready {v:E}(hx:v∈ball 0 r)(hk:k≤N) :
    iteratedFDeriv ℝ k (fun x=>∑' i,f i x) v= ∑' i,iteratedFDeriv ℝ k (f i) v:= iterated_at_sum isOpen_ball (convex_ball _ _|>.isPreconnected) (h.cash hm).2.1 h.proceeds hx k hk
lemma prices {v:E}(hx:v∈ball 0 r)(hk:k≤N) : ‖iteratedFDeriv ℝ k (fun x=>∑' i,f i x) v‖ ≤ C:= by
   have hp i: ‖iteratedFDeriv ℝ k (f i) v‖ ≤ h.book i:= (h.proceeds i _ hx).norm_le k hk
   have hh:= (h.cash hm).2.1.of_nonneg_of_le (fun i=>norm_nonneg (iteratedFDeriv ℝ k (f i) v)) hp
   rw [ready h hm hx hk]; exact (norm_tsum_le_tsum_norm hh).trans ((hh.tsum_le_tsum hp (h.cash hm).2.1).trans (h.cash hm).2.2)

include he
lemma gathering (q:ℕ)(hq:q≤N)(x:E): Summable (fun i=> summit (f i) q x) ∧ (summit (fun x:E=>∑' i,f i x) q x)=∑' i,summit (f i) q x:= by
   have hh(k:ℕ)(hk:k≤N):= h.reads hm (mem_ball_self he : (0:E)∈ball 0 r) hk
   let Z (k:ℕ)(i):=(k.factorial:ℝ)⁻¹ • (iteratedFDeriv ℝ k (f i) 0) (fun _=>x)
   have hf (k:ℕ)(hk:k≤q): Summable (Z k):= ((hh k (hk.trans hq)).mapL (ContinuousMultilinearMap.apply ℝ _ _ (fun _=>x))).const_smul _ -- implicit
   simp_rw [runes]; have he' : _:= summable_sum (s:=Finset.range (q+1)) (f:=Z) (fun i hi=> hf i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) -- check
   refine ⟨he',?_⟩; rw [Summable.tsum_finsetSum (f:=Z) (fun i (hi:i∈Finset.range (q+1))=> hf i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))]
   apply Finset.sum_congr rfl; intro i hi; have hi':i≤N:= le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hq; rw [h.ready hm (mem_ball_self he) hi',ContinuousMultilinearMap.tsum_eval (hh _ hi')]; exact (Summable.tsum_const_smul _ ((hh _ hi').mapL (ContinuousMultilinearMap.apply ℝ _ _ (fun _=>x)))).symm
end revenue
end YM.MatchingLedger.Mountain
