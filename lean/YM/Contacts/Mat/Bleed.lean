import YM.Contacts.Mat.Jet

/-! Only use Lagrange interpolation in a single coordinate at a time. Marked
seams require all *selected* evaluations to miss every tie in that dimension.
Choose stably positioned nodes above the request. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Mat
open Function Filter Metric Set Power Polynomial Lagrange
open scoped Topology BigOperators ContDiff
variable {α E:Type*} [NormedAddCommGroup E][NormedSpace ℝ E]
variable {n:ℕ}(x : Fin (n+1)→ℝ)
def bleed (i:Fin (n+1)) : ℝ:= (Lagrange.basis Finset.univ x i).eval 0
lemma onPower (h:Injective x) (m:ℕ)(hm:m ≤ n): ∑ i, bleed x i*(x i)^m= (0:ℝ)^m:=by
   let f : ℝ[X]:= X^m
   have he := Lagrange.eq_interpolate (f:=f) (s:=Finset.univ) (v:=x) h.injOn (by rw [degree_X_pow]; simp only [Finset.card_univ,Fintype.card_fin]; exact_mod_cast Nat.lt_succ_of_le hm)
   have ht:=congr_arg (Polynomial.eval 0) he
   rw [Lagrange.interpolate_apply,eval_finsetSum] at ht
   symm; simpa only [eval_mul,eval_C,f,eval_pow,eval_X,mul_comm,bleed] using ht -- mul_comm maybe unifies rhs sorting?
lemma onUnit (h:Injective x) (m:ℕ)(hm:m ≤ n): ∑ i, bleed x i*unitMonomial m (x i)= unitMonomial m 0:=by simp_rw [unitMonomial,mul_left_comm (bleed ..),← Finset.mul_sum,onPower x h m hm]
lemma combines_series (f: ℕ→ℝ→ E)(h:Injective x) : ∑ i, bleed x i • series f n 0 (x i)= f 0 0:=by
   rw [← series_center f 0 n]; unfold series
   simp_rw [Finset.smul_sum,sub_zero,smul_smul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j hj; rw [← Finset.sum_smul, onUnit x h j (show j≤n from Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
@[simp] lemma sums_one (h:Injective x) : ∑ i,bleed x i=1:=by simpa using onPower x h 0 (Nat.zero_le _)
variable {P:Pace α}{a b:ℝ}
structure Nodes (n:ℕ) (b:ℝ) where
    v : Fin (n+1)→ℝ
    starts i: v i∈ Icc 0 b
    apart i j:i≠j→ 1 ≤ ‖v i-v j‖
lemma Nodes.good (F:Nodes n b): Injective F.v:= fun i j h=> by by_contra H; have hv:= F.apart i j H; simp [h] at hv; norm_num at hv
lemma allowance (F:α→ Nodes n b): ∀ i:Fin (n+1), P.Priced 0 fun j=> bleed (F j).v i:= by
   intro i; simp_rw [bleed,Lagrange.basis,Lagrange.basisDivisor, eval_prod, eval_mul, eval_C,eval_sub,eval_X, zero_sub]
   let s:=Finset.univ.erase i
   have he k: P.Priced 0 (fun j=>(F j).v k):= Pace.Priced.from_bound b (Eventually.of_forall fun j=> by rw [Real.norm_of_nonneg ((F j).starts k).1]; exact ((F j).starts k).2)
   have ht (k) (h:k∈ s): P.Priced 0 (fun j=> ((F j).v i-(F j).v k)⁻¹):= Pace.Priced.from_bound 1 (Eventually.of_forall fun j=> by rw [norm_inv]; exact inv_le_one_of_one_le₀ ((F j).apart i k (Ne.symm (Finset.ne_of_mem_erase h))))
   have hx:= Pace.Priced.product s (fun k j=> ((F j).v i-(F j).v k)⁻¹ * -(F j).v k) (fun _=>0) (fun k h=> by simpa only [zero_add] using! (ht k h).mul (he k).neg)
   simpa only [Finset.sum_const_zero,eval_C] using hx
lemma approximates (F:α→ Nodes n b) (f:α→ℕ→ℝ→ E) (hb:0≤b)(h:∀ᶠ i in P.net, ∀ t∈Icc 0 b, ∀ j≤n, HasDerivAt (f i j) (f i (j+1) t) t)(he:∀ x:α→ℝ,(∀ᶠ i in P.net,x i∈ Icc 0 b)→ P.Priced a (fun i=>f i (n+1) (x i))) :
    P.Priced a fun i=> f i 0 0 - ∑ j, bleed (F i).v j • f i 0 ((F i).v j) :=by
    have hu (k:Fin (n+1)): P.Priced a (fun i=> f i 0 ((F i).v k)-series (f i) n 0 ((F i).v k)):= cost hb h he _ (Eventually.of_forall fun i=> (F i).starts k)
    apply (Pace.Priced.sum Finset.univ (fun j i=> bleed (F i).v j • (f i 0 ((F i).v j)-series (f i) n 0 ((F i).v j))) (fun j _=> ((allowance (P:=P) F j).smul (hu j)).shift (by ring))).neg.congr
    -- incorrect explicit C duplication
    filter_upwards with i; simp_rw [smul_sub,Finset.sum_sub_distrib,neg_sub, combines_series _ (f i) (F i).good]
end YM.Contacts.Mat
