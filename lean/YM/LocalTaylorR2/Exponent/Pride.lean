import YM.LocalTaylorR2.Exponent.Vesta
/-!
 # Dimension-independent estimates for the unprofiled field Taylor

 Keep PGA factors proportional to size of tensor, otherwise pay only
 total argument moments. Uses sup-norm when E is a family of fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Filter Function MeasureTheory Finset
open ConnectedActivityE6.Blaze Tensor Brush Work.G05
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {k j : ℕ} {x:E}

-- Keep this actual cost on the polynomial coefficients. Pay spatial radius
-- later. Don't use dimensions of E even in n-point argument Taylor.
def crown (j k:ℕ): ℝ:= ∑ i∈ range (j+1),(k.descFactorial i:ℝ)
lemma crown_pos : 0 ≤ crown j k:= sum_nonneg fun _ _=> Nat.cast_nonneg _
theorem shank (U : T E F k)(a:ℝ)(ha:1≤a)(hx:‖x‖≤a) (b:ℝ)(hp:‖U‖≤b) : Brush j (crown j k*b*a^k) 1 (diagonal U) x:=by
  let L:= ContinuousLinearMap.pi (fun _:Fin k => ContinuousLinearMap.id ℝ E)
  have ht y:‖L y‖≤‖y‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _=> le_rfl
  have he:‖L‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> by rw [one_mul]; exact ht _
  change Brush _ _ _ (U ∘ L) x; refine ⟨(diag_smooth ..).contDiffAt,zero_le_one,fun i hi=>?_⟩
  unfold normJ; rw [linear_pull _ (U.contDiff.contDiffAt),one_pow,mul_one]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  rw [prod_const,card_univ,Fintype.card_fin]; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he i) (norm_nonneg _)); rw [one_pow,mul_one]
  have h := U.norm_iteratedFDeriv_le i (L x); rw [Fintype.card_fin] at h; refine h.trans ?_
  have hb:0≤b:= (norm_nonneg _).trans hp; have hc:=crown_pos (j:=j) (k:=k)
  gcongr
  · exact single_le_sum (f:=fun i=> (k.descFactorial i:ℝ)) (fun _ _=> Nat.cast_nonneg _) (mem_range.mpr (Nat.lt_succ_of_le hi))
  · exact (pow_le_pow_left₀ (norm_nonneg _) ((ht _).trans hx) _).trans (pow_le_pow_right₀ ha (Nat.sub_le ..))
lemma thimble (U:T F G k) {g:E→F} {V : ℝ} {A : ℝ} (hv: 1 ≤ V)(h:‖U‖≤A)(hp:Brush j V 1 g x) :
   Brush j ((j.factorial*(crown j k*A*V^k))*(3*V)^j) 1 (diagonal U ∘g) x:=by
  have he:= hp.pine (shank U V hv hp.bound A h)
  have hk:= he.trim; exact hk.climb (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0≤1+(1+V)*1) (by linarith) _) he.nonneg) le_rfl
lemma tensorSize (f:E→F) {k t:ℕ} (h:k≤t) {A:ℝ} (hf:Brush t A 1 f 0): ‖Tensor.coeff f k 0‖≤ A := by
  unfold Tensor.coeff; rw [norm_smul, Real.norm_of_nonneg (by positivity : 0≤(k.factorial:ℝ)⁻¹)]; exact (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos k))).trans (by simpa using hf.order k h)
def stamp (j p:ℕ) (A v :ℝ):= ∑ k∈ range (p+1), ((j.factorial*(crown j k*A*v^k))*(3*v)^j)
lemma tactile (f:F→G) {g:E→F} {A V:ℝ}{p:ℕ}(h:Brush p A 1 f 0)(hg:Brush j V 1 g x)(hP:1≤V): Brush j (stamp j p A V) 1 (blockTaylor p f ∘g) x:= by
  simp_rw [blockTaylor, Function.comp_def, Finset.sum_apply]; exact spree (range (p+1)) _ _ zero_le_one (fun k hk=> thimble _ hP (tensorSize _ (Nat.le_of_lt_succ (mem_range.mp hk)) h) hg)
namespace Drifts
variable {B: Type} {p:B→ℝ} {f' : B→ E→ F} (he:∀ b,1≤ p b)
include he
lemma diagonalBody (U : T F G k) (hp:Drifts p f' x j): Drifts p (fun i x=> diagonal U (f' i x)) x j:= by
  obtain ⟨C,hC,n,h⟩:=hp.full
  let D:= 1+C; have hD:1 ≤ D:= le_add_of_nonneg_right hC
  refine ⟨_,show 0 ≤ j.factorial*(crown j k*‖U‖*D^k)*(3*D)^j from (by have h:=crown_pos (j:=j) (k:=k); positivity), n*k+n*j,?_⟩
  filter_upwards [h] with y hy b; let x:=p b; have hE:1≤x:=he _
  have ht : 1 ≤ D*x^n:= one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hE)
  have hb:= (thimble U ht le_rfl ((hy b).climb (show _ ≤ D*x^n from mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (zero_le_one.trans (one_le_pow₀ hE))) le_rfl))
  refine hb.climb ?_ le_rfl
  apply le_of_eq
  unfold x; simp only [mul_pow, pow_add, pow_mul]; ring_nf
lemma taylor (U:F→G) (hp:Drifts p f' x j)(d:ℕ): Drifts p (fun i x=> blockTaylor d U (f' i x)) x j:=by
  simp_rw [blockTaylor,Finset.sum_apply]; exact Drifts.all he _ (fun _ _=> hp.diagonalBody he _)
end Drifts
end YM.LocalTaylorR2.Exponent
