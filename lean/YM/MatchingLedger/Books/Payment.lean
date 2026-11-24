import YM.MatchingLedger.Books.Solve

/-!
# Finite horizon solver and numerical prices on all joint polynomial requests

Combined stencil norm already accounted for in the family W; this consumes the physical
posterior error producer. No assumptions on e.g. differentiability of the measure in the
coupling. Include truncation and coefficient identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Books.FPS
open Function Filter Matrix Finset MvPolynomial
open scoped BigOperators Classical
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {V : ℕ → Poly ι}
    {T : Fountain (V 0)} {g M : ℝ} {n : ℕ}

def forecast (T : Fountain (V 0))(g : ℝ)(n : ℕ): Prediction ι:= ∑ i∈antidiagonal n,g^i.2 • report V T i.2
lemma forecast_terms (q : ℕ)(p : Poly ι) : forecast T g q p=∑ i∈antidiagonal q,g^i.2*report V T i.2 p:= by simp only [forecast,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
lemma forecast_amount (q : ℕ) (p : Poly ι) : forecast T g q p=∑ i∈range (q+1), g^i * report V T i p:= by
  rw [forecast_terms,← Finset.Nat.sum_antidiagonal_swap]; exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _=>g^i* report V T i p) q
lemma forecast_lone (q : ℕ) : forecast T g q 1=1:=by rw [forecast_amount]; simp [returns_unit,mul_ite]

lemma static_line (q : ℕ) (p : Poly ι) (j : ι) : ley V j (forecast T g) p g q=0:= by
  have h : ∑ i∈ antidiagonal q,g^i.2 * forecast T g i.1 (slope V j i.2 *p) =
      ∑ i∈antidiagonal q, ∑ k∈antidiagonal i.2, g^k.2*(g^k.1*report V T k.1 (slope V j k.2 * p)):=by
    simp_rw [forecast_terms,Finset.mul_sum]; exact triple (fun _ b c=>g^c*(g^b*report V T b (slope V j c*p))) q
  rw [ley,h,forecast_terms]; apply neg_eq_iff_add_eq_zero.mp; simp_rw [← Finset.sum_neg_distrib, report_sd, mul_neg, neg_neg, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun k h=>?_
  rw [← mem_antidiagonal.mp h,pow_add]; ring
omit [DecidableEq ι] [Fintype ι] in
lemma stamp_sub (q : ℕ)(p : Poly ι) (j : ι)(W Y : ℕ → Prediction ι) :
    ley V j (W-Y) p g q= ley V j W p g q - ley V j Y p g q := by simp only [ley,Pi.sub_apply,LinearMap.sub_apply,mul_sub,sum_sub_distrib]; ring

-- exact form to compare to in SD on posterior; zero vertex intentionally *not* counted twice.
omit [DecidableEq ι] [Fintype ι] in
lemma dynamic_test (W : Prediction ι) (q : ℕ)(p : Poly ι)(j : ι)(g:ℝ)(V:ℕ→Poly ι) :
    ley V j (fun _=> W) p g q= W (force V j p + ∑ i∈ range (q+1), g^i • (slope V j i * p)) := by
  unfold ley; rw [← Finset.Nat.sum_antidiagonal_swap, _root_.map_add,_root_.map_sum]; apply congrArg₂ (·+·) rfl; simp_rw [_root_.map_smul,smul_eq_mul]; exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _=>g^i* W (slope V j i*p)) q

variable (L : License V T M n) (W : Prediction ι)
    (hg : 0≤g) (he : W 1=1) (hy : ∀ (q:ℕ) (v:Token ι), q+heft v+1 ≤ n→∀ i:ι, ‖ley V i (fun _=>W) (mark v) g q‖ ≤ M*g^(q+1))

namespace License
include L
lemma printed : Stamp V 1 M (report V T) n := by
  have he : 1≤M:= L.one
  constructor
  · intro q _; rw [returns_unit]; split_ifs <;> simp_all; linarith
  intro q m _ i; rw [ley,report_sd]; simp; exact zero_le_one.trans he

lemma charged {g:ℝ} {W:ℕ→ Prediction ι} (hp:0≤g) (h:Stamp V g M W n) (q:ℕ)(p:Poly ι) (l:ℕ) (h':p.totalDegree ≤ l)(hq:q+l≤ n) :
    ‖W q p‖ ≤ fare p*(bill n M q l*g^(q+1)):= by
  apply by_mark _ _ _ h'; intro m hm
  apply (L.stamped_mark hp h q m (by omega)).trans; apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp _); unfold bill; exact pow_le_pow_right₀ (board_one n L.one) (Nat.add_le_add_right (Nat.add_le_add_left hm _) _)

lemma formal_cost (q l:ℕ)(p:Poly ι) (h:p.totalDegree ≤ l)(hp:q+l≤ n) : ‖report V T q p‖ ≤ fare p * bill n M q l:=by
  simpa only [one_pow,mul_one] using L.charged zero_le_one L.printed q p l h hp

include hg hy he
lemma expenditure : Stamp V g M ((fun _=>W)-forecast T g) n:= by
  have hh:1≤M:=L.one
  constructor
  · intro q hq; rw [Pi.sub_apply,LinearMap.sub_apply,he,forecast_lone]; simp [mul_nonneg (zero_le_one.trans hh) (pow_nonneg hg _)]
  intro q v h i; rw [stamp_sub,static_line,sub_zero]; exact hy q v h i

lemma invoice (q : ℕ) (p : Poly ι) (l: ℕ) (hp : p.totalDegree ≤ l) (hq : q+l ≤ n) :
    ‖W p - forecast T g q p‖ ≤ fare p * (bill n M q l * g^(q+1)):= L.charged hg (L.expenditure W hg he hy) q p l hp hq -- fix grammar
end License
end YM.MatchingLedger.Books.FPS
