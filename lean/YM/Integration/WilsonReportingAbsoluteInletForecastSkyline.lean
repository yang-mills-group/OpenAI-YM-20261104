import YM.Integration.WilsonReportingAbsoluteInletForecastCapital

/-! One finite degree schedule controls both full coefficient sums. The
resulting constants are chosen before the kinetic course and its dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastSkyline
open PowerSeries FormalBulk08.Wine Finset WilsonReportingAbsoluteInletForecastBooks
open WilsonReportingAbsoluteInletForecastCapital
theorem prices (n:ℕ)(grade:ℕ→ℕ):∃B:ℝ,∃d:ℕ,0 ≤ B ∧
    ∀(D:PowerSeries ℝ) (t:ℝ),1 ≤ t→(∀i,i ≤ n→|coeff i (bookU D)| ≤ t^(grade i))→
      mass n (bookU D)+mass n (bookH D) ≤ B*t^d:=by
  let m:=(range (n+1)).sup grade
  let B:ℝ:=(n+1)+(2:ℝ)^n
  have mcap (i:ℕ)(hi:i ≤ n):grade i ≤ m:=
    Finset.le_sup (s:=range (n+1)) (f:=grade) (mem_range.mpr (by omega))
  refine ⟨B,m*(n+1),by dsimp [B];positivity,?_⟩
  intro D t t1 filed
  let M:=t^m
  have M1:1 ≤ M:=one_le_pow₀ t1
  have M0:0 ≤ M:=zero_le_one.trans M1
  have rows:=control D n M0 (fun i hi=>(filed i hi).trans (pow_le_pow_right₀ t1 (mcap i hi)))
  have upper:(1+M)^n ≤ (2:ℝ)^n*M^n:=by rw [←mul_pow];apply pow_le_pow_left₀ (by linarith only [M0]);linarith only [M1]
  have Mn:1 ≤ M^n:=one_le_pow₀ M1
  have a:M ≤ M^(n+1):=by rw [pow_succ];nlinarith only [mul_nonneg (sub_nonneg.mpr Mn) M0]
  have b:M^n ≤ M^(n+1):=by rw [pow_succ];nlinarith only [mul_nonneg (pow_nonneg M0 n) (sub_nonneg.mpr M1)]
  calc
    _ ≤ (n+1)*M+(2:ℝ)^n*M^n:=add_le_add rows.1 (rows.2.trans upper)
    _ ≤ (n+1)*M^(n+1)+(2:ℝ)^n*M^(n+1):=
      add_le_add (mul_le_mul_of_nonneg_left a (by positivity)) (mul_le_mul_of_nonneg_left b (by positivity))
    _ = B*t^(m*(n+1)):=by dsimp [B,M]; rw [pow_mul]; ring
end YM.Integration.WilsonReportingAbsoluteInletForecastSkyline
