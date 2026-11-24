import YM.Integration.FVA1Physical.Wilson.SourceClock

/-! Bounds for the physical coupling change on rooted, marked coefficient
banks. The price depends on the fixed orders and the clock jet; the number
of sites and the locations of the fields never enter the price. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG
open MSbar MSbar.Cacao MSbar.Bakery MSbar.Wave MSbar.Rolling.Price MSbar.Whisk MSbar.Rolling MSbar.Lis MSbar.CrossH MSbar.Measuring
open scoped Classical Topology BigOperators
variable {σ : Type} [Fintype σ] [DecidableEq σ] {c:Side}

theorem homogeneous_vault (l:σ→Site c) (W:Finset (Site c)) {α C:ℝ} {s h:ℕ} {f:Pot σ}
    (fund:Vault l W α s h 0 f C) (d:ℕ) : Vault l W α s h 0 (homogeneousComponent d f) C := by
  refine ⟨fund.1,fun k hk=>le_trans ?_ (fund.2 k hk)⟩
  apply shiny
  intro L _
  unfold rate
  rw [←CrossH.tours,←CrossH.tours,Bronze.jewels]
  split
  · rfl
  rw [abs_zero,mul_zero]
  exact mul_nonneg (effect ..).le (abs_nonneg _)

def sourceClockFee (p m:ℕ) (D:ℝ) := ∑ j ∈ range (p+1),∑ d ∈ range (m+1), Bronze.term p d j D

private theorem term0 (p d j:ℕ) {D:ℝ} (hD:1 ≤ D) : 0 ≤ Bronze.term p d j D := by
  have h:=zero_le_one.trans hD
  unfold Bronze.term
  positivity

theorem sourceClock_vault (l:σ→Site c) (W:Finset (Site c)) {α C D:ℝ} (s h p m:ℕ)
    (T:PowerSeries (Pot σ)) (b:PowerSeries ℝ) (unit:PowerSeries.coeff 0 b=1) (bound:Bronze.brim p b D)
    (hD:1 ≤ D) (input:∀ j ≤ p,Vault l W α s h 0 (PowerSeries.coeff j T) C) (i:ℕ) (hi:i ≤ p) :
    Vault l W α s h 0 (PowerSeries.coeff i (sourceClock m b T)) (sourceClockFee p m D*C) ∧
    (PowerSeries.coeff i (sourceClock m b T)).totalDegree ≤ m := by
  have hC:0 ≤ C:=(input 0 (Nat.zero_le _)).1
  simp only [sourceClock,PowerSeries.coeff_mk]
  constructor
  · let cost j:=∑ d∈range (m+1),Bronze.term p d j D*C
    have each (j:ℕ) (hj:j∈range (i+1)):Vault l W α s h 0 (sourceFare m b T j (i-j)) (cost j) := by
      apply Quote.total
      intro d _
      apply Quote.widen (Quote.mulR (homogeneous_vault l W (input j ((Nat.lt_succ_iff.mp (mem_range.mp hj)).trans hi)) d) _)
      · exact mul_le_mul_of_nonneg_right (Bronze.star b d j unit bound hD (i-j) ((Nat.sub_le ..).trans hi)) hC
      · rfl
    apply Quote.widen (Quote.total _ _ cost each) _ le_rfl
    unfold sourceClockFee
    simp only [sum_mul]
    exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ hi))
      (fun j _ _=>sum_nonneg fun d _=>mul_nonneg (term0 p d j hD) hC)
  apply totalDegree_finsetSum_le
  intro j _
  apply totalDegree_finsetSum_le
  intro d hd
  exact (totalDegree_smul_le ..).trans ((homogeneousComponent_isHomogeneous ..).totalDegree_le.trans
    (Nat.lt_succ_iff.mp (mem_range.mp hd)))

end YM.Integration.FVA1Physical.Wilson
