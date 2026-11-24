import YM.Integration.FVA1Physical.Wilson.SourceClockRows
import YM.MSbar.Bristol.Dot
import YM.MSbar.Wave.Rider

/-! A finite, support-weighted residual for the actual scalar coupling ratio
of an interacting scene. This carries arbitrary marked initial coefficients,
including a nonzero degree-zero coupling term. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG
open MSbar MSbar.Cacao MSbar.Bakery MSbar.Wave MSbar.Rolling.Price MSbar.Whisk MSbar.Rolling MSbar.Lis MSbar.CrossH MSbar.Measuring
open Bristol
open MSbar.Bakery.Portal
open scoped Classical Topology BigOperators
variable {σ : Type} [Fintype σ] [DecidableEq σ] {c:Side}

omit [Fintype σ] [DecidableEq σ] in
theorem source_clock_read (b:PowerSeries ℝ) (T:PowerSeries (Pot σ)) (m n:ℕ) (x:View σ) (t:ℝ) :
    taste n (picture x (sourceClock m b T)) t = ∑ i∈range (n+1),t^i*(∑ d∈range (m+1),
      taste (n-i) (b^d*b⁻¹^i) t*MvPolynomial.eval x (homogeneousComponent d (PowerSeries.coeff i T))) := by
  let g(i j:ℕ):= ∑ d∈range (m+1), PowerSeries.coeff j (b^d*(b⁻¹^i)) *
    MvPolynomial.eval x (homogeneousComponent d (PowerSeries.coeff i T))
  let F(i j):=t^(i+j:ℕ)*g i j
  have hx(a):t^a*PowerSeries.coeff a (picture x (sourceClock m b T))=∑ i∈ range (a+1),F i (a-i):=by
    unfold picture sourceClock
    rw [PowerSeries.coeff_map,PowerSeries.coeff_mk,map_sum,mul_sum]
    apply sum_congr rfl
    intro i hi
    have hi:=mem_range.mp hi
    unfold sourceFare F g
    rw [show i+(a-i)=a by omega]
    simp only [_root_.map_sum,← C_mul',_root_.map_mul,eval_C]
  unfold taste
  simp_rw [hx]
  rw [aims]
  apply sum_congr rfl
  intro i _
  unfold F g
  simp_rw [pow_add,mul_assoc,←Finset.mul_sum]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _=>?_
  rw [Finset.sum_mul]
  exact sum_congr rfl fun a _=>by ring

def scalarResetRow (m p:ℕ) (b:PowerSeries ℝ) (t u:ℝ) (T:PowerSeries (Pot σ)) :=
  ∑ i∈range (p+1),∑ d∈range (m+1), pegsK b t u p i d • homogeneousComponent d (PowerSeries.coeff i T)

def scalarResetFee (m p:ℕ) (A:ℝ):=∑ i∈range (p+1),∑ d∈range (m+1),tonK A d i

omit [DecidableEq σ] in
theorem scalar_reset_identity (m p:ℕ) (b:PowerSeries ℝ) (t u:ℝ) (T:PowerSeries (Pot σ))
    (deg:∀ j ≤ p,(PowerSeries.coeff j T).totalDegree ≤ m) (x:View σ) :
    taste p (picture (u • x) T) (t/u) - taste p (picture x (sourceClock m b T)) t =
      MvPolynomial.eval x (scalarResetRow m p b t u T) := by
  rw [source_clock_read,taste,scalarResetRow,map_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  rw [picture,PowerSeries.coeff_map]
  have eqn:=buys m _ (deg j (Nat.lt_succ_iff.mp (mem_range.mp hj)))
  nth_rw 1 [←eqn]
  rw [map_sum,mul_sum,mul_sum,←sum_sub_distrib,map_sum]
  apply sum_congr rfl
  intro d _
  rw [hene u 0 x d _,←C_mul',_root_.map_mul,eval_C]
  unfold pegsK
  rw [div_eq_mul_inv,mul_pow]
  ring

theorem scalar_reset_vault (l:σ→Site c) (W:Finset (Site c)) {a C A t u:ℝ} (s h m p:ℕ)
    (b:PowerSeries ℝ) (T:PowerSeries (Pot σ)) (unit:PowerSeries.coeff 0 b=1)
    (t₀:0 ≤ t) (t₁:t ≤ 1) (u₀:0 < u) (ua:|u| ≤ A) (ui:u⁻¹ ≤ A) (one:1 ≤ A)
    (bf:Belt p b ≤ A) (bi:Belt p b⁻¹ ≤ A)
    (price:∀ j ≤ p,Vault l W a s h 0 (PowerSeries.coeff j T) C) :
    Vault l W a s h 0 (scalarResetRow m p b t u T)
      (scalarResetFee m p A*((|u-taste p b t|+(A+1)*t^(p+1))*C)) := by
  let E:=|u-taste p b t|+(A+1)*t^(p+1)
  have a₀:=zero_le_one.trans one
  have c₀:0 ≤ C:=(price 0 (Nat.zero_le _)).1
  have kw (d i:ℕ):0 ≤ tonK A d i:=by unfold tonK;positivity
  have scal (d i:ℕ) (hi:i ≤ p):|pegsK b t u p i d| ≤ tonK A d i * E := by
    by_cases iz:i=0
    · subst i
      have v:=scent b u unit u₀ ua ui bf bi one t₀ t₁ d 0
      simp only [pegsK,pow_zero,one_mul,Nat.sub_zero] at v ⊢
      exact v.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (le_mul_of_one_le_left (pow_nonneg t₀ _) (le_add_of_nonneg_left a₀))) (kw d 0))
    · have v:=costsK b u t u₀ bf bi ua ui one t₀ t₁ unit i (Nat.pos_of_ne_zero iz) hi d
      exact v.trans (mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_of_le_one_left (abs_nonneg _) t₁) le_rfl) (kw d i))
  unfold scalarResetFee scalarResetRow
  simp only [sum_mul]
  apply Quote.total
  intro i hi
  apply Quote.total
  intro d _
  apply Quote.widen (Quote.mulR (homogeneous_vault l W (price i (Nat.lt_succ_iff.mp (mem_range.mp hi))) d) _) _ le_rfl
  exact (mul_le_mul_of_nonneg_right (scal d i (Nat.lt_succ_iff.mp (mem_range.mp hi))) c₀).trans_eq (mul_assoc _ _ _)

end YM.Integration.FVA1Physical.Wilson
