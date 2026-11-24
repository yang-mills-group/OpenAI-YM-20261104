import YM.Integration.WilsonLocalTerminalSpectator
import YM.Integration.WilsonLocalInheritedWeights
import YM.Integration.WilsonLocalReportingExpense

/-! Fix the zero-angle comparison at the same compact exterior pivot.
Only the sampled field must meet the original occupied face condition. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalChartAnchor
open Filter Finset Set Lattice RG Wilson Tree RG16 Precision PertExtension PertExtension.Series
open PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open WilsonLocalConditionalResidue WilsonLocalTerminalWeights
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}

theorem zero_expense {ι:Type} [Fintype ι] (p:ℕ) {H W g:ℝ} (hH:0 ≤ H) (hW:0 ≤ W) (hg:0 ≤ g) (X:ι→G.Color) :
    expense p H W g X 0 ≤ expense p H W g X X := by
  have each (k:ℕ) (hk:0 < k) :
      (∑i:ι,(‖X i‖^k+‖(0:ι→G.Color) i‖^k)) ≤ ∑i:ι,(‖X i‖^k+‖X i‖^k) := by
    apply sum_le_sum;intro i _
    exact add_le_add le_rfl (by simpa only [Pi.zero_apply,norm_zero,zero_pow hk.ne'] using pow_nonneg (norm_nonneg (X i)) k)
  exact add_le_add (mul_le_mul_of_nonneg_left (each (p+1) (by omega)) (by positivity))
    (mul_le_mul_of_nonneg_left (each (p+3) (by omega)) (by positivity))

theorem weight_zero (P:ChartRatio G) (hp:LocalRatio P) {c f:Side} {S:StepData c f}
    (T:Forest S.ratio) (B:Finset T.Free) (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El)
    (g:ℝ) (ρ:Config G f→ℝ) (hρ:∀U,0 < ρ U) : 0 < weight P ρ T B v g 0 := by
  unfold WilsonLocalConditionalResidue.weight;apply mul_pos _ (hρ _);rw [smul_zero]
  apply Finset.prod_pos;intro e _
  change 0 < Chart.fee P 0
  rw [WilsonConditionalTaylorThermalLocalHaar.anchor P hp];exact hp.scale

theorem increment (p:ℕ) {D ε g:ℝ} (d0:0 ≤ D) (ep:0 < ε) (g0:0 ≤ g) (small:g ≤ 1)
    (rate:D ≤ min 1 (ε/2)*g^p) : Real.exp D-1 ≤ ε*g^p := by
  let a:=min 1 (ε/2)
  have a0:0 ≤ a:=le_min zero_le_one (by positivity)
  have hi:D ≤ 1:=calc
    _ ≤ a*g^p:=rate
    _ ≤ a*1:=mul_le_mul_of_nonneg_left (pow_le_one₀ g0 small) a0
    _ ≤ _:=by rw [mul_one];exact min_le_left ..
  have bounds:=Real.abs_exp_sub_one_le ((abs_of_nonneg d0).trans_le hi)
  calc
    _ ≤ 2*D := (le_abs_self _).trans (bounds.trans_eq (by rw [abs_of_nonneg d0]))
    _ ≤ 2*(a*g^p) := mul_le_mul_of_nonneg_left rate (by norm_num)
    _=(2*a)*g^p:=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_right (by have m:a ≤ ε/2:=min_le_right ..;linarith) (pow_nonneg g0 _)

end YM.Integration.WilsonLocalChartAnchor
