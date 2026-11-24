import YM.MatchingLedger.Ensemble
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Internal and external color slots, numerical polynomial library

Absolute monomial coefficient norm, preserving degrees. Will be used with derivatives of an
*extensive* action; the derivative support matters (cannot spend a factor of the volume in
an absolute sum). The norm here does not encode location/valuation information; further
annotations used in that application.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Books
open Function Filter Set MvPolynomial
open scoped Topology Classical BigOperators ContDiff

variable {ι : Type*}
abbrev Poly (ι : Type*) := MvPolynomial ι ℝ
abbrev Token (ι : Type*) := ι →₀ ℕ

def fare (p : Poly ι) := ∑ s∈p.support, ‖p.coeff s‖
def mark (s : Token ι) : Poly ι := monomial s 1
def heft (s : Token ι) : ℕ := s.sum fun _ e=>e

theorem mark_weight (s : Token ι) : (mark s).totalDegree=heft s := totalDegree_monomial s one_ne_zero
theorem fare_nn (p : Poly ι) : 0 ≤ fare p := Finset.sum_nonneg fun _ _=> norm_nonneg _
theorem fare_monomial (s : Token ι) (c : ℝ) : fare (monomial s c)= ‖c‖:= by by_cases h:c=0 <;> simp [fare,h,support_monomial]
theorem fare_C (c : ℝ) : fare (ι:=ι) (C c)= ‖c‖ := fare_monomial _ _ -- replace implicit
theorem fare_X (i : ι) : fare (X i)=1 := by rw [X,fare_monomial,norm_one]
theorem fare_mark (s : Token ι) : fare (mark s)=1:= by rw [mark,fare_monomial,norm_one]
theorem fare_zero : fare (0 : Poly ι)=0 := by simp [fare]

lemma fare_extend (s : Finset (Token ι))(p : Poly ι) (h:p.support⊆s) :
    fare p=∑ i∈s, ‖p.coeff i‖:= Finset.sum_subset h fun i _ hi=>by rw [notMem_support_iff.mp hi,norm_zero]
lemma fare_add (p q : Poly ι) : fare (p+q) ≤ fare p + fare q := by
  rw [fare_extend _ _ (support_add ..), fare_extend _ p (Finset.subset_union_left (s₂:=q.support)),
    fare_extend _ q (Finset.subset_union_right (s₁:=p.support)), ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _=> (coeff_add i p q) ▸ norm_add_le _ _
lemma fare_sum {α : Type*} (s : Finset α) (p : α → Poly ι) : fare (∑ i∈s,p i) ≤ ∑ i∈s, fare (p i):=by
  induction s using Finset.induction_on with
  | empty=> simp [fare_zero]
  | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (fare_add _ _).trans (add_le_add le_rfl ih)
lemma fare_mul (p q : Poly ι) : fare (p*q) ≤ fare p * fare q := by
  nth_rw 1 [p.as_sum]; nth_rw 1 [q.as_sum]; rw [Finset.sum_mul]; apply le_trans (fare_sum ..)
  -- caution not unfold fare on the left
  change (∑ s∈p.support, fare _) ≤ (∑ s∈p.support, ‖p.coeff s‖) * fare q
  rw [Finset.sum_mul]; refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]; apply le_trans (fare_sum ..); apply le_of_eq; simp_rw [monomial_mul,fare_monomial,norm_mul]; unfold fare; rw [Finset.mul_sum]
lemma fare_scale (c : ℝ) (p : Poly ι) : fare (c • p)≤‖c‖ * fare p := by rw [show c • p=C c*p from Algebra.smul_def ..,← fare_C]; apply fare_mul
lemma fare_neg (p : Poly ι) : fare (-p)≤ fare p := by simpa using fare_scale (-1) p
lemma fare_sub (p q : Poly ι) : fare (p-q) ≤ fare p+fare q := by rw [sub_eq_add_neg]; exact (fare_add p (-q)).trans (add_le_add le_rfl (fare_neg q))
lemma fare_product {α : Type*}(s : Finset α) (p : α→Poly ι) : fare (∏ i∈s,p i) ≤ ∏ i∈s, fare (p i):= by
  induction s using Finset.induction_on with
  | empty=> rw [Finset.prod_empty,Finset.prod_empty, show (1: Poly ι)= C 1 from (map_one C).symm, fare_C,norm_one]
  | insert i s hi ih=> rw [Finset.prod_insert hi,Finset.prod_insert hi]; exact (fare_mul ..).trans (mul_le_mul_of_nonneg_left ih (fare_nn _))
lemma fare_pow (p : Poly ι) (k : ℕ) : fare (p^k) ≤ (fare p)^k:= by simpa using fare_product (Finset.range k) (fun _=>p)

-- Algebra and derivative helpers. Keep all mixed derivatives after matching.
section diff

variable [Fintype ι]
lemma heft_univ (t : Token ι) : heft t=∑ i,t i := Finsupp.sum_fintype _ _ (fun _=>rfl)
lemma heft_add (s t : Token ι) : heft (s+t)=heft s+heft t:= by simp_rw [heft_univ,Finsupp.add_apply]; exact Finset.sum_add_distrib
omit [Fintype ι] in
lemma heft_single (i : ι) (n : ℕ) : heft (Finsupp.single i n)=n:=Finsupp.sum_single_index (by rfl)
lemma heft_zero (s : Token ι) : heft s=0↔ s=0:=by rw [heft_univ, Finset.sum_eq_zero_iff]; simp [DFunLike.ext_iff]
lemma index_le (s : Token ι)(i : ι) : s i ≤ heft s:= by rw [heft_univ]; exact Finset.single_le_sum (fun i _=>Nat.zero_le (s i)) (Finset.mem_univ i)
lemma heft_diminish (s : Token ι)(i : ι) (h:0<s i): heft (s-Finsupp.single i 1)+1 = heft s := by
  nth_rw 2 [← heft_single i 1]; rw [← heft_add,tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h)]
omit [Fintype ι] in
lemma term_remove {s : Token ι}{i : ι}(h:0<s i) : X i * mark (s-Finsupp.single i 1)=mark s := by
  have hp:=tsub_add_cancel_of_le (show Finsupp.single i 1 ≤ s from Finsupp.single_le_iff.mpr h); unfold X mark; rw [monomial_mul,one_mul,add_comm,hp]
lemma fare_pderiv_mark (s : Token ι) (i : ι) : fare (pderiv i (mark s)) ≤ heft s := by
  rw [mark,pderiv_monomial,fare_monomial,one_mul]; simpa only [Real.norm_natCast,Nat.cast_le] using! index_le s i
lemma total_pderiv_mark (s : Token ι) (i : ι) : (pderiv i (mark s)).totalDegree ≤ heft s - 1:= by
  rw [mark,pderiv_monomial,one_mul]; by_cases h : s i=0; · simp [h]
  rw [totalDegree_monomial _ (by exact_mod_cast h)]; change heft _ ≤ _; have hh:= heft_diminish s i (Nat.pos_of_ne_zero h); omega

omit [Fintype ι] in
lemma line_mark (c:ℝ)(s : Token ι): monomial s c = c • mark s:=by rw [mark,smul_monomial,smul_eq_mul,mul_one]
lemma fare_gradient {q : Poly ι} (i : ι){d : ℕ} (h : q.totalDegree ≤ d): fare (pderiv i q) ≤ d * fare q := by
  nth_rw 1 [q.as_sum]; rw [_root_.map_sum]; apply le_trans (fare_sum ..)
  unfold fare; rw [Finset.mul_sum]; refine Finset.sum_le_sum (fun s hs=>?_)
  have hm: heft s≤d:= (le_totalDegree hs).trans h; change fare _ ≤ _
  rw [line_mark,(pderiv i).map_smul,mul_comm (d:ℝ)]; exact (fare_scale ..).trans (mul_le_mul_of_nonneg_left ((fare_pderiv_mark s i).trans (Nat.cast_le.mpr hm)) (norm_nonneg _))
lemma total_gradient {p : Poly ι}(i : ι){d:ℕ}(h : p.totalDegree ≤ d) : (pderiv i p).totalDegree ≤ d-1 := by
  nth_rw 1 [p.as_sum]; rw [_root_.map_sum]; refine totalDegree_finsetSum_le (fun s hs => ?_)
  rw [line_mark,(pderiv i).map_smul]; exact (totalDegree_smul_le ..).trans ((total_pderiv_mark s i).trans (Nat.sub_le_sub_right ((le_totalDegree hs).trans h) _))
omit [Fintype ι] in
lemma gradient_local {p : Poly ι} (i : ι) : (pderiv i p).vars ⊆ p.vars := by
  intro j hj; obtain ⟨m,hm,hJ⟩:= (mem_vars_iff_mem_support j).mp hj
  have ht:=mem_support_iff.mp hm; rw [coeff_pderiv] at ht
  exact (mem_vars_iff_mem_support j).mpr ⟨_,mem_support_iff.mpr (show p.coeff _ ≠ 0 from left_ne_zero_of_mul ht),
    Finsupp.mem_support_iff.mpr (by rw [Finsupp.add_apply]; have h0:= Finsupp.mem_support_iff.mp hJ; omega)⟩
end diff

/-- Sup 'infinite norm' on coordinates, polynomial itself stays multilinear at its physical
slots *before* overlaps; not asserting such multilinearity on the resulting link evaluation. -/
abbrev Field (ι : Type*) := ι → ℝ
abbrev Prediction (ι : Type*) := Module.Dual ℝ (Poly ι)

def read (x : Field ι) : Prediction ι := (aeval x).toLinearMap
lemma read_apply (x : Field ι)(p : Poly ι) : read x p=eval x p:= by change aeval x p=eval x p; simp

-- functional pricing after all-slot estimates
lemma by_mark (L : Prediction ι) {d:ℕ}{M : ℝ} (h : ∀ s : Token ι, heft s ≤ d → ‖L (mark s)‖ ≤ M) (p : Poly ι) (hp : p.totalDegree ≤ d) : ‖L p‖ ≤ fare p * M:=by
  nth_rw 1 [p.as_sum]; rw [map_sum]; apply (norm_sum_le ..).trans
  unfold fare; rw [Finset.sum_mul]; refine Finset.sum_le_sum (fun i hi=>?_)
  rw [show monomial i (p.coeff i) = p.coeff i • mark i by rw [mark,smul_monomial,smul_eq_mul,mul_one],map_smul,norm_smul]
  exact mul_le_mul_of_nonneg_left (h _ ((le_totalDegree hi).trans hp)) (norm_nonneg _)

lemma read_term (p : Token ι) (x : Field ι){M : ℝ}(_hm:0≤M)(hx:∀ i∈p.support,‖x i‖≤ M): ‖read x (mark p)‖ ≤ M^heft p:=by
  rw [read_apply, mark, eval_monomial, one_mul]; unfold Finsupp.prod
  rw [Real.norm_eq_abs, Finset.abs_prod]; unfold heft Finsupp.sum; rw [← Finset.prod_pow_eq_pow_sum]; apply Finset.prod_le_prod (fun i _=> abs_nonneg _); intro i hi; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hx i hi) _
lemma read_bounded {p : Poly ι} {s : Finset ι}{d :ℕ}{M : ℝ}(hp:p.totalDegree≤d)(hs:p.vars⊆s)(hm:1≤M)(x:Field ι)(hy:∀ i∈s,‖x i‖≤ M): ‖read x p‖ ≤ fare p * M^d := by
  nth_rw 1 [p.as_sum]; rw [map_sum]; apply (norm_sum_le ..).trans; unfold fare; rw [Finset.sum_mul]; apply Finset.sum_le_sum
  intro z hz
  rw [show monomial z (p.coeff z) = p.coeff z • mark z by rw [mark,smul_monomial,smul_eq_mul,mul_one],map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left ((read_term z x (zero_le_one.trans hm) (fun i hi=> hy i (hs ((mem_vars_iff_mem_support _).mpr ⟨_,hz,hi⟩)))).trans (pow_le_pow_right₀ hm ((le_totalDegree hz).trans hp))) (norm_nonneg _)

end YM.MatchingLedger.Books
