import YM.Integration.WilsonReceivedCloseNamedWallet
import YM.Integration.WilsonReceivedLogWindow
import YM.Comparison.RG02.Valence.Volume

/-! Complete occupied-source bills on the same finite logarithmic Wilson table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseFaceBudget
open Finset Marker Extra.Trajectories Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Order
open scoped BigOperators

variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}

omit [Fintype V] in
theorem empty_physical (Y : Poly R) (unit : Y.part R.quiet=1) (n : ℕ) :
    (logTo n Y).part R.quiet=0 := by
  rw [logTo,Poly.part_sum]
  apply sum_eq_zero
  intro i _
  rw [Poly.part_smul,pow_succ,Poly.quiet_mul,part_sub]
  simp [unit]

theorem empty_finite {r : ℕ} (W : Grade R r) (unit : UnitLeading W) (z : ℂ) :
    (value z (logMarked W)).part R.quiet=0 := by
  rw [vpart]
  apply sum_eq_zero
  intro i _
  have h : (observe R r (logMarked W) i).part R.quiet=0 := by
    unfold observe
    split
    · change _*(logMarked W).part _=0
      rw [Valence.log_m_part _ unit,Join.left_pair,if_pos rfl,mul_zero]
    · rfl
  rw [h,mul_zero]

omit [Fintype V] in
theorem product {w:V→ℝ} (wp:∀v,0<w v) {active:Finset V} {fee:ℝ} (s:R.Mode)
    (covered:s.val⊆active) (enrolled:∀v∈active,(w v)⁻¹ ≤ fee) : (Poly.toll w s)⁻¹ ≤ fee^s.val.card := by
  unfold Poly.toll
  rw [← Finset.prod_inv_distrib,← Finset.prod_const]
  exact Finset.prod_le_prod (fun v _=>inv_nonneg.mpr (wp v).le) (fun v hv=>enrolled v (covered hv))

theorem mass {t base w price mass : ℝ} (tp:0<t) (bp:0<base) (wp:0<w)
    (edge:t⁻¹ ≤ 3*base⁻¹) (bought:w⁻¹ ≤ price) (pay:t*(w*mass) ≤ 1) :
    mass ≤ (3*base⁻¹)*price := by
  have direct : mass ≤ (t*w)⁻¹ := by
    rw [← one_div,le_div_iff₀ (mul_pos tp wp)]
    calc
      mass*(t*w)=t*(w*mass) := by ring
      _ ≤ 1 := pay
  rw [mul_inv] at direct
  exact direct.trans (mul_le_mul edge bought (inv_nonneg.mpr wp.le)
    (mul_nonneg (by norm_num) (inv_nonneg.mpr bp.le)))

end YM.Integration.WilsonReceivedCloseFaceBudget
