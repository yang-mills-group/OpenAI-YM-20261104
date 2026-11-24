import YM.Work.G05.Taylor
import YM.LocalTaylorR2.Test
/-! # Post-halo dimension-independent jet estimate at actual neighborhood.
 For any eventual cost-series of local primitives with bounded Brush on
 that chart, this is the precise power which may be spent for Taylor in
 ALL Lie arguments, not in individual occurrences. Allows probe order above series limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Mesh
open ConnectedActivityE6.Blaze Tensor Work.G05 Metric Set Finset Filter
open scoped ContDiff Topology BigOperators Classical
variable {E F V W : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup V] [NormedAddCommGroup W]
variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] [NormedSpace ℝ W]
variable {k n j d i : ℕ} {A : ℝ} {t : ℝ} {f : E→ V}
lemma silence (Z : Tensor.T E V k) (x:E) (h:k<n): iteratedFDeriv ℝ n (diagonal Z) x=0:=by
  let L := ContinuousLinearMap.pi (fun _:Fin k=>ContinuousLinearMap.id ℝ E)
  change iteratedFDeriv ℝ n (_ ∘ (L: E→Fin k→E)) x=0
  rw [linear_pull L (Z.contDiff.contDiffAt (n:=n)),show iteratedFDeriv ℝ n Z (L x)=0 from ?_]; rfl
  have hp:= Z.norm_iteratedFDeriv_le n (L x)
  simpa [Nat.descFactorial_of_lt h] using hp
lemma peace (f : E→V) (x:E) (h:d<k): iteratedFDeriv ℝ k (blockTaylor d f) x=0:=by
  rw [blockTaylor,iteratedFDeriv_sum_apply (fun i _=> (diag_smooth _ _).contDiffAt)] -- binder?
  exact sum_eq_zero fun i hi=> silence _ _ ((Nat.lt_succ_iff.mp (mem_range.mp hi)).trans_lt h)
lemma smash {i b c : ℕ} (hx:0≤t)(hA:0≤A)
    (hz:∀ k<b,iteratedFDeriv ℝ k f 0=0)
    (hh:∀ u,‖u‖≤t→ ContDiffAt ℝ (↑b) f u ∧ ‖iteratedFDeriv ℝ b f u‖ ≤ A) (p : i+c=b):
    ∀ u,‖u‖≤t → ‖iteratedFDeriv ℝ i f u‖ ≤ A*t^c:=by
  induction c generalizing i with
  | zero => intro u hu; specialize hh u hu; simp only [Nat.add_zero] at p; subst b; simpa using hh.2 
  | succ c ih =>
    intro u hu; have hp v (hv : v∈ Metric.closedBall (0:E) t) : ‖v‖ ≤ t:= mem_closedBall_zero_iff.mp hv
    have hl (v : E)(hv:v∈Metric.closedBall (0:E) t): ‖fderiv ℝ (iteratedFDeriv ℝ i f) v‖ ≤ A*t^c:=by
      rw [norm_fderiv_iteratedFDeriv]; exact ih (by omega : i+1+c=b) v (hp v hv)
    have h:= (convex_closedBall (0:E) t).norm_image_sub_le_of_norm_fderiv_le (fun i' h=> (hh i' (hp i' h)).1.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr (by omega))) hl (mem_closedBall_self hx) (mem_closedBall_zero_iff.mpr hu)
    rw [hz i (by omega),sub_zero,sub_zero] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hu (by positivity)).trans_eq (by ring))
lemma rapping {f:E→V} (hx:0≤t)(hh:∀ u,‖u‖≤t→Brush (d+1) A 1 f u) (u:E)(hu:‖u‖≤t)(hp:i≤d+1) :
    ‖iteratedFDeriv ℝ i (f-blockTaylor d f) u‖ ≤ A*t^(d+1-i):=by
  have h₀ : Brush (d+1) A 1 f 0 := hh _ (by simpa)
  refine smash hx h₀.nonneg (b:=d+1) (fun k h=> ?_) (fun x hx=> ?_) (by omega) u hu
  · have hz : ContDiffAt ℝ k f 0:= (h₀.smaller (by omega : k≤_)).smooth
    rw [iteratedFDeriv_sub_apply hz (blockTaylor_contDiff _ _ _).contDiffAt,blockTaylor_jets (h₀.smaller (d.le_succ)).smooth _ (by omega),sub_self]
  have ht:= hh x hx
  refine ⟨ht.smooth.sub (blockTaylor_contDiff _ _ _).contDiffAt,?_⟩
  rw [iteratedFDeriv_sub_apply ht.smooth (blockTaylor_contDiff _ _ _).contDiffAt,peace _ _ (by omega),sub_zero]
  simpa only [one_pow,mul_one] using ht.order _ (Nat.le_refl _)
lemma costAlong {x:E}(p : 0≤t)(ht:t≤1)(he:‖x‖≤1)
    (h:∀ x,‖x‖≤ t→Brush (j+d+1) A 1 f x): Brush j (A*t^(d+1)) 1 (fun x=> (f-blockTaylor d f) (t•x)) x := by
  let L:= t•ContinuousLinearMap.id ℝ E
  have hA:0≤A:= (h 0 (by rwa [norm_zero])).nonneg
  have hL: ‖L‖≤ t:=by unfold L; rw [norm_smul,Real.norm_of_nonneg p]; exact mul_le_of_le_one_right p ContinuousLinearMap.norm_id_le
  have hx': ‖L x‖ ≤ t:=(ContinuousLinearMap.le_opNorm _ _).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans (mul_le_of_le_one_right p he))
  have hf:= h (L x) hx'
  change Brush j (A*t^(d+1)) 1 ((f-blockTaylor d f) ∘ (L:E→E)) x
  have hu (i) (hi:i≤j): ContDiffAt ℝ i (f-blockTaylor d f) (L x):=((hf.smaller (by omega : i≤_)).smooth.sub (blockTaylor_contDiff d _ _).contDiffAt)
  refine ⟨(hu j le_rfl).comp _ L.contDiff.contDiffAt,zero_le_one,fun i hi=>?_⟩
  unfold normJ; rw [linear_pull _ (hu _ hi),one_pow, mul_one]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [prod_const, card_univ,Fintype.card_fin]
  apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL i) (norm_nonneg _))
  by_cases he : i≤d+1
  · refine le_trans (mul_le_mul_of_nonneg_right (rapping p (fun x hx=> (h x hx).smaller (by omega)) (L x) hx' he (f:=f)) (pow_nonneg p i)) ?_
    rw [mul_assoc,← pow_add,Nat.sub_add_cancel he]
  rw [iteratedFDeriv_sub_apply (hf.smaller (by omega : i≤j+d+1)).smooth (blockTaylor_contDiff _ _ _).contDiffAt,peace f _ (by omega),sub_zero]
  exact mul_le_mul (by simpa only [one_pow,mul_one] using hf.order i (by omega)) (pow_le_pow_of_le_one p ht (by omega)) (pow_nonneg p _) hA
lemma priced {g:W→E} {x:W} (p: 0<t)(ht:t≤1)
    (h:∀ x,‖x‖≤ t→Brush (j+d+1) A 1 f x) (hf:Brush j t 1 g x): Brush j ((j.factorial*A)*((1+((1+1)*1):ℝ))^j*t^(d+1)) 1 (fun x=>(f-blockTaylor d f) (g x)) x :=by
  let g' : W→E:= t⁻¹ • g
  have he : Brush j 1 1 g' x:=by simpa only [Real.norm_of_nonneg (by positivity : 0≤ t⁻¹),inv_mul_cancel₀ p.ne'] using! hf.smul t⁻¹
  have hy : (fun x=> (f-blockTaylor d f) (t•g' x)) =fun x=> (f-blockTaylor d f) (g x):=by ext x; simp [g',Pi.smul_apply,smul_smul,p.ne']
  rw [←hy]; refine (he.pine (costAlong p.le ht he.bound h)).trim.climb (le_of_eq ?_) le_rfl; ring
end YM.LocalTaylorR2.Mesh
