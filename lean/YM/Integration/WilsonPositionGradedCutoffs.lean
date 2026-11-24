import YM.Integration.WilsonOrdinaryPivotAsymptotic

/-! A simultaneous smooth realization at countably many finite field horizons.
The original norm-controlled cutoff is applied to a padded pair; the padded
norm is independent of the horizon, so every inclusion receives the same
scalar for each coefficient, at every positive coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionGradedCutoffs
open Function Filter Set Finset
open scoped Topology ContDiff Classical BigOperators
variable {E : ℕ→Type*} [∀ d,NormedAddCommGroup (E d)] [∀d,NormedSpace ℝ (E d)]
variable (a : ∀ d,ℕ→E d)

private def size (d : ℕ) : ℝ := 1+∑n∈range (d+1),‖a d n‖
omit [∀d,NormedSpace ℝ (E d)] in
private theorem good (d : ℕ) : 0<size a d := by
  have h : 0≤∑n∈range (d+1),‖a d n‖ := sum_nonneg (fun _ _=>norm_nonneg _)
  unfold size; linarith
private def scaled (d n : ℕ) : E d := (size a d)⁻¹ • a d n
private def cap (n : ℕ) : ℝ := 1+∑ d∈range (n+1),‖scaled a d n‖
private theorem floor (n : ℕ) : 1≤cap a n :=
  le_add_of_nonneg_right (sum_nonneg (fun _ _=>norm_nonneg _))
private theorem bound (d n : ℕ) : ‖scaled a d n‖≤cap a n := by
  by_cases h:d≤n
  · have ht:= single_le_sum (f:=fun d=>‖scaled a d n‖) (fun i _=>norm_nonneg _) (mem_range.mpr (Nat.lt_succ_of_le h))
    unfold cap; linarith
  · have ht:= single_le_sum (f:=fun n=>‖a d n‖) (fun i _=>norm_nonneg _) (mem_range.mpr (by omega : n<d+1))
    apply le_trans _ (floor a n)
    rw [scaled,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (good a d).le),←div_eq_inv_mul]
    exact (div_le_one (good a d)).mpr (by unfold size;linarith)

private def padded (d n : ℕ) : E d × ℝ := (scaled a d n, cap a n)
private theorem norm_padded (d n : ℕ) : ‖padded a d n‖=cap a n := by
  rw [Prod.norm_def]
  change max ‖scaled a d n‖ ‖cap a n‖=cap a n
  rw [Real.norm_of_nonneg (zero_le_one.trans (floor a n)),max_eq_right (bound a d n)]

private def width (n : ℕ) : ℝ := 2^(n+1)*(1+cap a n)+(n:ℝ)+1
def weight (n : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (2-width a n*t)*t^n

private theorem wide (n : ℕ) : (n:ℝ)≤width a n := by
  have hc : 0≤cap a n := zero_le_one.trans (floor a n)
  have hp : 0≤ (2:ℝ)^(n+1)*(1+cap a n) := mul_nonneg (by positivity) (by linarith)
  unfold width;linarith

theorem finite {t : ℝ} (ht : 0<t) :
    ∃ N : ℕ,∀ n : ℕ,N≤n→weight a n t=0 := by
  obtain ⟨N,hN⟩:=exists_nat_ge (2/t)
  refine ⟨N,fun n hn=>?_⟩
  have h:2≤width a n*t := (div_le_iff₀ ht).mp (hN.trans ((by exact_mod_cast hn : (N:ℝ)≤n).trans (wide a n)))
  unfold weight
  rw [Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr h),zero_mul]

/-- All horizons use this single sequence of scalar cutoffs. -/
def field (d : ℕ) (t : ℝ) : E d := size a d • (WilsonOrdinaryPivotAsymptotic.realizer (padded a d) t).1

private theorem first (d : ℕ) (s : Finset ℕ) (w : ℕ→ℝ) :
    size a d • (∑n∈s,w n • padded a d n).1 = ∑ n∈s,w n • a d n := by
  simp only [Prod.fst_sum,Prod.smul_fst,Finset.smul_sum]
  apply sum_congr rfl
  intro n _
  change size a d • w n • (size a d)⁻¹ • a d n = _
  rw [smul_comm (size a d) (w n)]
  apply congrArg (fun x : E d=>w n • x)
  rw [smul_smul,mul_inv_cancel₀ (good a d).ne',one_smul]

theorem exactly {t : ℝ} {N : ℕ} (cut : ∀ n : ℕ,N≤n→weight a n t=0) (d : ℕ) :
    field a d t=∑n∈range N,weight a n t • a d n := by
  have hm : WilsonOrdinaryPivotAsymptotic.realizer (padded a d) t =
      ∑ n∈range N, weight a n t • padded a d n := by
    change (∑' n:ℕ,(Real.smoothTransition (2-(2^(n+1)*(1+‖padded a d n‖)+(n:ℝ)+1)*t)*t^n) • padded a d n)=_
    simp_rw [norm_padded]
    change (∑' n:ℕ,weight a n t • padded a d n)=_
    exact tsum_eq_sum (fun n hn=>by rw [cut n (not_lt.mp (fun h=>hn (mem_range.mpr h))),zero_smul])
  unfold field
  rw [hm]
  exact first a d _ _

theorem smooth (d : ℕ) : ContDiffOn ℝ ∞ (field a d) (Ioi 0) :=
  contDiffOn_const.smul (WilsonOrdinaryPivotAsymptotic.smooth (padded a d)).fst

/-- A single choice of fields precedes every truncation, in every grade. -/
theorem expansion (d q : ℕ) :
    ∃ A : ℝ,0≤A ∧ ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖field a d t-∑n∈range (q+1),t^n • a d n‖ ≤ A*t^(q+1) := by
  let u:=padded a d
  refine ⟨size a d*(‖u (q+1)‖+2),mul_nonneg (good a d).le (by positivity),?_⟩
  filter_upwards [WilsonOrdinaryPivotAsymptotic.expansion u q] with t h
  let x:=WilsonOrdinaryPivotAsymptotic.realizer u t
  let y:=WilsonOrdinaryPivotAsymptotic.truncation u q t
  have hy:size a d • y.1=∑n∈range (q+1),t^n • a d n:=first a d _ _
  rw [←hy]
  change ‖size a d • x.1-size a d • y.1‖≤_
  rw [←smul_sub,norm_smul,Real.norm_of_nonneg (good a d).le]
  have hs : ‖x.1-y.1‖ ≤ ‖x-y‖ := by rw [Prod.norm_def]; exact le_max_left ..
  exact (mul_le_mul_of_nonneg_left (hs.trans h) (good a d).le).trans_eq (mul_assoc ..).symm

end YM.Integration.WilsonPositionGradedCutoffs

