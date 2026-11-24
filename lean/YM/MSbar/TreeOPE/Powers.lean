import YM.MSbar.TreeOPE.Mixed
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
/-! # Weight projections, dilations, and pairing remainder budget -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.OPE
open Function Filter Set Asymptotics
open MvPolynomial Finsupp Next.Rank.Normal
open scoped Topology BigOperators Classical ContDiff
variable {V W : Type}

variable (w : V→ℕ)
def readW (r : ℂ) (v : V) : V →₀ ℂ := Finsupp.single v (r^w v)
def scale (r : ℂ) : poly V →ₐ[ℂ] poly V:= exchange (readW w r)
abbrev tier (n : ℕ) : poly V →ₗ[ℂ] poly V := weightedHomogeneousComponent w n
abbrev pureW (n : ℕ) (p : poly V) := IsWeightedHomogeneous w p n
lemma scaled (r : ℂ) (v : V) : scale w r (X v)=r^w v • X v:= by unfold scale readW; rw [exchange_x,glyph,linearCombination_single]
lemma scaled_pure (r : ℂ) (n) (p) (h : pureW w n p) : scale w r p= r^n • p:= by
  refine IsWeightedHomogeneous.induction_on (motive:=fun p _=>scale w r p = r^n • p) ?_ ?_ ?_ h
  · simp
  · intro p q _ _ hp hq; simp only [_root_.map_add,hp,hq,smul_add]
  intro k x hk; rw [← hk, monomial_eq, _root_.map_mul, show scale w r (C x)=C x from exchange_c _ _,Finsupp.prod,_root_.map_prod]
  simp_rw [_root_.map_pow, scaled, smul_pow,← pow_mul]; rw [Finset.prod_smul,Finset.prod_pow_eq_pow_sum,mul_smul_comm,weight_apply,Finsupp.sum]; congr! 2; simp [mul_comm]
lemma allLevels {K : ℕ} (p : poly V) (H : weightedTotalDegree w p ≤ K) : ∑ i∈Finset.range (K+1),tier w i p=p:= by
  have ht : Function.support (fun i=> tier w i p) ⊆ (Finset.range (K+1):Set ℕ) := by
    intro x hx; apply Finset.mem_range.mpr; refine lt_of_not_ge (fun h=>?_); exact hx (weightedHomogeneousComponent_eq_zero x p (lt_of_le_of_lt H h))
  rw [← finsum_eq_sum_of_support_subset _ ht]; apply sum_weightedHomogeneousComponent

def approximant (p : poly V) (r : ℂ) (n : ℕ):poly V:= ∑ i∈Finset.range (n+1),r^i • tier w i p
lemma rescale_full {K : ℕ} (p : poly V) (r : ℂ) (H : weightedTotalDegree w p≤K) : scale w r p=approximant w p r K:= by
  conv_lhs => rw [← allLevels w p H,_root_.map_sum];
  apply Finset.sum_congr rfl; intro i _; exact scaled_pure w r i _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

lemma slabAsymp (p : poly V) (L : poly V→ₗ[ℂ] ℂ) (m : ℕ) : (fun r:ℝ=> L (scale w (r:ℂ) p)-∑ i∈Finset.range (m+1),(r:ℂ)^i* L (tier w i p)) =O[𝓝 0] (fun r=>r^(m+1)):= by
  let H:=max m (weightedTotalDegree w p); have he:m≤H:= le_max_left ..
  have h : Finset.range (m+1) ⊆ Finset.range (H+1):= Finset.range_mono (Nat.succ_le_succ he)
  simp_rw [rescale_full (K:=H) w p _ (le_max_right ..),approximant,_root_.map_sum,_root_.map_smul, smul_eq_mul,show ∀ f:ℕ→ℂ,(∑ i∈Finset.range (H+1), f i) - (∑ i∈Finset.range (m+1), f i) = _ from fun f=>(eq_sub_of_add_eq (Finset.sum_sdiff h)).symm]
  apply IsBigO.sum; intro i hi; simp_rw [mul_comm _ (L _)]; apply IsBigO.const_mul_left
  have hh : m+1 ≤ i:= Nat.le_of_not_gt fun hz=> (Finset.mem_sdiff.mp hi).2 (Finset.mem_range.mpr hz)
  refine IsBigO.of_bound 1 ?_; filter_upwards [(continuous_norm.tendsto (0:ℝ)).eventually (ge_mem_nhds (show ‖(0:ℝ)‖ <1 from by norm_num))] with r hr; rw [one_mul,norm_pow,norm_pow,Complex.norm_real]; apply pow_le_pow_of_le_one (norm_nonneg _) hr hh
end YM.MSbar.OPE

namespace YM.MSbar.OPE
open Function Filter Set Asymptotics
open MvPolynomial Finsupp Next.Rank.Normal
open scoped Topology BigOperators Classical ContDiff
variable {V A B : Type} (w : V→ℕ)

-- equality through truncated output grade H

def through (H : ℕ) (p q : poly V) := ∀ i≤ H,tier w i p=tier w i q
lemma through_add {H : ℕ} {p q u v} (h : through w H p q) (ht : through w H u v): through w H (p+u) (q+v):= by intro i hi; rw [_root_.map_add,_root_.map_add,h i hi, ht i hi]
private def High (H : ℕ): Submodule ℂ (poly V) := restrictSupport ℂ {a|(H < Finsupp.weight w a)}
private lemma high {H : ℕ} {p : poly V} : p ∈ High w H ↔ through w H p 0:= by
  unfold High through; rw [MvPolynomial.mem_restrictSupport_iff]; constructor
  · intro he i hi; apply MvPolynomial.ext; intro a; rw [_root_.map_zero,coeff_weightedHomogeneousComponent]; split_ifs with h
    · by_contra hg; rw [coeff_zero] at hg; have ht : H < i := h ▸ he (MvPolynomial.mem_support_iff.mpr hg); exact hi.not_gt ht
    exact (coeff_zero _).symm
  intro hw i hi; by_contra hh; apply MvPolynomial.mem_support_iff.mp hi
  have ht:= congr_arg (MvPolynomial.coeff i) (hw (weight w i) (le_of_not_gt hh))
  simpa only [tier, _root_.map_zero, coeff_zero, coeff_weightedHomogeneousComponent,ite_true,eq_self] using ht
private lemma high_mul {H : ℕ} (p q : poly V) (h : p∈ High w H): p*q∈ High w H := by
  rw [High, mem_restrictSupport_iff] at h ⊢
  intro a ha; have he:= MvPolynomial.support_mul (p:=p) (q:=q); specialize he ha; obtain ⟨i,hi,j,hj,rfl⟩:= Finset.mem_add.1 he; exact lt_of_lt_of_le (show H<weight w i from h hi) (by rw [map_add]; omega)
private lemma diff {H : ℕ} {p q : poly V} : p-q∈ High w H ↔ through w H p q:= by rw [high]; unfold through; simp only [map_sub, _root_.map_zero,sub_eq_zero]
lemma through_mul {H : ℕ} {p q a b} (h : through w H p q) (ht : through w H a b): through w H (p*a) (q*b):= by
  apply (diff w).mp; rw [show p*a-q*b=(p-q)*a+(a-b)*q from by ring]; exact (High w H).add_mem (high_mul w _ _ ((diff w).2 h)) (high_mul w _ _ ((diff w).2 ht))
lemma through_eval {H : ℕ} (L K : poly B→ₐ[ℂ] poly V) (h : ∀ i,through w H (L (X i)) (K (X i))) (p : poly B): through w H (L p) (K p):= by
  induction p using MvPolynomial.induction_on with
  | C c => rw [algHom_C, algHom_C]; exact fun _ _=>rfl
  | add p q hp hq=> rw [_root_.map_add,_root_.map_add]; exact through_add w hp hq
  | mul_X p i ih=> rw [_root_.map_mul,_root_.map_mul]; exact through_mul w ih (h i)
end YM.MSbar.OPE
