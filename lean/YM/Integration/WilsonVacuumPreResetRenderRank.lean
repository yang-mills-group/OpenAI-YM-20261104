import YM.Integration.WilsonVacuumPreResetRenderIncome
import YM.Integration.WilsonVacuumPreResetPeriodEntries

/-! The true filed rank, its physical pitch and the two inverse Gaussian
powers enter the same per-row estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetRenderRank
open Function Finset RG Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open IterationFour.Vacuum Extra.Iteration WilsonVacuumPreResetPeriodEntries
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}

def weight (g p:ℝ)(d v:ℕ):ℝ:=(g^2)⁻¹*p*(g/Real.sqrt p)^(d+2-v)

theorem atom (B:BudgetPoint)(a:PrismA G)(σ C g p A:ℝ)(cap:ℕ)(positive:0<g)(unit:g≤1)
    (large:1≤A)(temperature:1/2≤p)(top:p≤2)(grade:3≤a.grade)(limit:a.grade≤cap)
    (angle:B.threshold≤2*g*A)(cash:|C|≤3*A)
    (bill:|FundedCorrectedPeriod.credit B σ C a|≤2*A^2*B.threshold^(a.rise+2)* |C|):
    |weight g p a.grade (a.rise+2)| * |FundedCorrectedPeriod.credit B σ C a|≤
      12*2^(cap+2)*g^3*A^(cap+5):=by
  let k:=a.rise+2
  let j:=a.grade-a.rise
  have re:a.rise≤a.grade:=a.rankA
  have degree:j+k=a.grade+2:=by dsimp [j,k];omega
  have order':k≤cap+2:=by dsimp [k];omega
  have pp:0<p:=by linarith
  have half:(1:ℝ)/2≤Real.sqrt p:=(Real.le_sqrt (by norm_num) pp.le).2 (by nlinarith)
  have c0:0≤g/Real.sqrt p:=by positivity
  have span:|g/Real.sqrt p|≤2*g:=by
    rw [abs_of_nonneg c0]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr pp)).2
    nlinarith only [mul_nonneg (sub_nonneg.mpr half) positive.le]
  have w:|weight g p a.grade (a.rise+2)|≤(g^2)⁻¹*2*(2*g)^j:=by
    unfold weight
    have same:a.grade+2-(a.rise+2)=j:=by dsimp [j];omega
    rw [same,abs_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg g)),abs_of_pos pp,abs_pow]
    gcongr
  have Apos:0≤A:=zero_le_one.trans large
  have kcost:|FundedCorrectedPeriod.credit B σ C a|≤2*A^2*(2*g*A)^k*(3*A):=by
    apply bill.trans
    gcongr
    exact B.threshold_pos.le
  have pw:(2*g)^j*(2*g)^k=(2*g)^(a.grade+2):=by rw [←pow_add,degree]
  have gg:(g^2)⁻¹*(2*g)^(a.grade+2)=2^(a.grade+2)*g^a.grade:=by
    rw [mul_pow,pow_add g _ 2]
    field_simp
    rw [pow_add]
    ring
  calc
    _ ≤ ((g^2)⁻¹*2*(2*g)^j)*(2*A^2*(2*g*A)^k*(3*A)):=by
      apply mul_le_mul w kcost (abs_nonneg _)
      positivity
    _ = 12*((g^2)⁻¹*((2*g)^j*(2*g)^k))*(A^k*A^3):=by rw [mul_pow (2*g) A];ring
    _ = 12*2^(a.grade+2)*g^a.grade*A^(k+3):=by rw [pw,gg,←pow_add];ring
    _ ≤ 12*2^(cap+2)*g^3*A^(cap+5):=by
      have temp:g^a.grade≤g^3:=pow_le_pow_of_le_one positive.le unit grade
      have two:(2:ℝ)^(a.grade+2)≤2^(cap+2):=pow_le_pow_right₀ (by norm_num) (by omega)
      have rent:A^(k+3)≤A^(cap+5):=pow_le_pow_right₀ large (by omega)
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left two (by norm_num)) temp (by positivity) (by positivity)) rent (by positivity) (by positivity)

end YM.Integration.WilsonVacuumPreResetRenderRank
