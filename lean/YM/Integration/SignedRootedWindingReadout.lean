import YM.WilsonCoeffUV.Marked.Capture.AnalyticBound
import YM.Push.ABSOLUTE_SUMS.Basic

/-! Independently chosen complex test functions against the actual signed winding current. The same joint measure carries every real and imaginary component and every rooted position. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedRootedWindingReadout
open Function Filter Finset MeasureTheory Set Lattice RG Laurent WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Soil WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos
open scoped BigOperators Classical Topology
variable {ι α : Type} [DecidableEq ι] {D : ι→ℕ} (J : Finset ι) {o : ι} {j r : ℕ} {σ B : ℝ}

/-- Scalar and imaginary test directions remain independent at every original mark. -/
abbrev Tests (D : ι→ℕ) := ∀a,(Scroll (D a) × Scroll (D a))

def test (v : Tests D) (s : J→ Bool) (a : ι) : Scroll (D a) := if h:a∈J then if s ⟨a,h⟩ then (v a).2 else (v a).1 else (v a).1

def phase (s : J→ Bool) : ℂ := ∏a:J,if s a then Complex.I else 1

def read (v : Tests D) (P : Pen D J) : ℂ := ∑s:J→ Bool,phase J s*(touch (fun a=>page _ (test J v s a)) J P:ℝ)

/-- Evaluate the signed finite-minus-cover difference on the identical test. -/
theorem read_sub (v : Tests D) (P Q : Pen D J) : read J v (P-Q)=read J v P-read J v Q := by
  unfold read
  simp only [map_sub,Complex.ofReal_sub,mul_sub,sum_sub_distrib]

def amplitude (v : Tests D) : ℝ := ∏a:J,(‖page _ (v a).1‖+‖page _ (v a).2‖)

omit [DecidableEq ι] in
private theorem pts_le (v : Tent D) (b : Post D) : ‖pts J v b‖≤∏a∈J,‖page _ (v a)‖ := by
  unfold pts
  rw [norm_mul,norm_prod,show ‖positiveP b.1‖=1 by cases b.1 <;> norm_num [positiveP],one_mul]
  exact prod_le_prod (fun _ _=>norm_nonneg _) fun a _=>creased (v a) (Nat.le_of_lt_succ (b.2 a).1.1.isLt) _ _

/-- Exact operator estimate for the complex extension of the original signed real current; no independent bound is imposed on the two kernels in its difference. -/
theorem coupon (v : Tests D) (P : Pen D J) (μ : Measure (Post D)) [IsFiniteMeasure μ]
    (h : ∀u:Tent D,touch (fun a=>page _ (u a)) J P=∫b,pts J u b ∂μ) :
    ‖read J v P‖≤amplitude J v*μ.real univ := by
  let A (a : J) (t : Bool) : ℝ := if t then ‖page _ (v a.val).2‖ else ‖page _ (v a.val).1‖
  have hp (s : J→ Bool) : ‖phase J s‖=1 := by unfold phase;rw [norm_prod]; simp only [apply_ite norm,Complex.norm_I,norm_one,ite_self,prod_const_one]
  have hm (s : J→ Bool) : ‖touch (fun a=>page _ (test J v s a)) J P‖≤(∏a:J,A a (s a))*μ.real univ := by
    rw [h]
    apply (norm_integral_le_of_norm_le_const (Eventually.of_forall (pts_le J (test J v s)))).trans_eq
    congr 1
    rw [←Finset.prod_coe_sort]
    refine prod_congr rfl fun a _=>?_ 
    by_cases hh : s a <;> simp [test,A,a.property,hh]
  apply (norm_sum_le ..).trans
  simp_rw [norm_mul,hp,one_mul,Complex.norm_real]
  calc
    _ ≤ ∑s:J→ Bool,(∏a:J,A a (s a))*μ.real univ := sum_le_sum fun s _=>hm s
    _ = amplitude J v*μ.real univ := by
      rw [←sum_mul,←Fintype.prod_sum]
      apply congrArg (fun z:ℝ=>z*μ.real univ)
      apply prod_congr rfl
      intro a _
      rw [Fintype.sum_bool]
      exact add_comm _ _

/-- A bounded test of the entire spatial coefficient table may vary independently at each full relative rooted address. -/
theorem rows {P : (ι→ Cover)→ Ten (Pen D J) (Cloth α) j} (h : PostMark J o j P σ B r) (x : Cover)
    (v : Fence α J o j→ Tests D) (U : ℝ) (hU : 0≤U) (hu : ∀i,amplitude J (v i)≤U)
    (ξ : Fence α J o j→ℂ) (hξ : ∀i,‖ξ i‖≤1) :
    SumBudget (fun i:Fence α J o j=>lineOut (toe J o x i.1) J o i.2^r*Real.exp (σ*Syn terrain (toe J o x i.1) J i.2)*‖ξ i*read J (v i) (towerV J o j P x i)‖) (U*B) := by
  obtain ⟨μ,hm,he,hb⟩ := h x
  apply Push.AbsoluteSums.budget_mono (Push.AbsoluteSums.budget_scale hU hb)
  · intro i;exact mul_nonneg (mul_nonneg (pow_nonneg (by unfold lineOut;positivity) _) (Real.exp_pos _).le) (norm_nonneg _)
  intro i
  letI := (hm i).2
  have hz : ‖ξ i * read J (v i) (towerV J o j P x i)‖≤U*(μ i).real univ := calc
    _ ≤ ‖read J (v i) (towerV J o j P x i)‖ := by rw [norm_mul];exact mul_le_of_le_one_left (norm_nonneg _) (hξ i)
    _ ≤ _ := (coupon J (v i) _ _ (he i)).trans (mul_le_mul_of_nonneg_right (hu i) (measureReal_nonneg))
  exact (mul_le_mul_of_nonneg_left hz (mul_nonneg (pow_nonneg (by unfold lineOut;positivity) _) (Real.exp_pos _).le)).trans_eq (by ring)

/-- Every absolutely summable signed test of the winding row has the same purchased price. -/
theorem tested {P : (ι→ Cover)→ Ten (Pen D J) (Cloth α) j} (ho : o∈J) (hs : 0≤σ) (h : PostMark J o j P σ B r)
    (x : Cover) (v : Fence α J o j→ Tests D) (U : ℝ) (hU : 0≤U) (hu : ∀i,amplitude J (v i)≤U)
    (ξ : Fence α J o j→ℂ) (hξ : ∀i,‖ξ i‖≤1) :
    Summable (fun i:Fence α J o j=>ξ i*read J (v i) (towerV J o j P x i)) ∧
      ‖∑'i:Fence α J o j,ξ i*read J (v i) (towerV J o j P x i)‖≤U*B := by
  have hh := rows J h x v U hU hu ξ hξ
  have hn := Push.AbsoluteSums.budget_mono hh (fun _=>norm_nonneg _) (fun i=>le_mul_of_one_le_left (norm_nonneg _) (one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (lineBound (p:=toe J o x i.1) ho i.2).1) (Real.one_le_exp (mul_nonneg hs (Nat.cast_nonneg _)))))
  exact ⟨hn.2.1.of_norm,(norm_tsum_le_tsum_norm hn.2.1).trans hn.2.2⟩

/-- One original coefficient with every independently specified test, before summing the other marked locations or field coordinates. -/
theorem point {P : (ι→ Cover)→ Ten (Pen D J) (Cloth α) j} (ho : o∈J) (hs : 0≤σ) (h : PostMark J o j P σ B r)
    (x : Cover) (i : Fence α J o j) (v : Tests D) : ‖read J v (towerV J o j P x i)‖≤amplitude J v*B := by
  have hU : 0≤amplitude J v := prod_nonneg fun _ _=>add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc (k : Fence α J o j) : ‖(Pi.single i (1:ℂ) : Fence α J o j→ℂ) k‖≤1 := by by_cases hk:k=i <;> simp [hk]
  have H := (tested J ho hs h x (fun _=>v) _ hU (fun _=>le_rfl) _ hc).2
  rw [tsum_eq_single i (fun k hk=>by simp [hk])] at H
  simpa only [Pi.single_eq_same,one_mul] using H

end YM.Integration.SignedRootedWindingReadout
