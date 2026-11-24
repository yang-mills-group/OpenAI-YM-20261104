import YM.Integration.WilsonReceivedCloseChainFunding

/-! One joint radius and retention charge for the complete three-name gallery. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralPrice
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG16 QuadraticLocal.Advent
open Function Filter Finset Lattice Wilson RG Tree QuadraticLocal AllOrder AllOrder.Floe
open AllOrder.Transit WheelP PhysicalNext.Repeat.Boulevard Extra.Histories Pert.Asymptotics
open scoped Classical BigOperators Topology

theorem charge (B:ℕ→ℝ) {i t:ℕ} (it:i<t)
    (one:∀j,1 ≤ B j) {d Ω:ℝ}
    (d0:0 ≤ d) (dmax:d ≤ ∏j∈Ico i t,(B j)^2*(B (j+1))^7)
    (o0:0 ≤ Ω) (page:Ω ≤ B i) {s a:ℕ} (limit:s ≤ a) :
    d^3*Ω^s ≤ ∏j∈Ico i t,((B j)^2*(B (j+1))^7)^(3+a) := by
  let step := fun j:ℕ=>(B j)^2*(B (j+1))^7
  let cost := ∏j∈Ico i t,step j
  have pos (j:ℕ) : 1 ≤ step j :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (one j)) (one_le_pow₀ (one (j+1)))
  have inner : i∈Ico i t := mem_Ico.mpr ⟨le_rfl,it⟩
  have first : step i ≤ cost := by
    calc
      step i = ∏j∈Ico i t,(if j=i then step j else (1:ℝ)) := by simp [inner]
      _ ≤ cost := Finset.prod_le_prod (fun j _=>by
        split
        · exact zero_le_one.trans (pos j)
        · exact zero_le_one) (fun j _=>by
        split
        · exact le_rfl
        · exact pos j)
  have base : B i ≤ step i := (show B i ≤ (B i)^2 by
      simpa only [pow_one] using pow_le_pow_right₀ (one i) (by decide:1 ≤ 2)).trans
    (le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans (one i)) _)
      (one_le_pow₀ (one (i+1))))
  have c0 : 1 ≤ cost := (pos i).trans first
  have head : Ω^s ≤ cost^a := (pow_le_pow_left₀ o0 (page.trans (base.trans first)) s).trans
    (pow_le_pow_right₀ c0 limit)
  calc
    d^3*Ω^s ≤ cost^3*cost^a := mul_le_mul (pow_le_pow_left₀ d0 dmax 3) head
      (pow_nonneg o0 _) (pow_nonneg (zero_le_one.trans c0) _)
    _ = _ := by rw [←pow_add];exact Finset.prod_pow .. |>.symm

variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "B" => budgetR R

include simple in
/-- The terminal old rent, reset multiplier and all lost original wallet radii are
paid by one stage product at the preselected close-window cost. -/
theorem original (degree a q:ℕ) {Q η ε:ℝ} (cap:0 ≤ Q) (loss:0 < η) (ep:0 ≤ ε) :
    ∀ᶠ t:ℕ in atTop,∀ m ≤ t, PaceR.Close R degree Q m t → ∀N per:ℕ,t<N →
      ∀ i, m ≤ i → i<t → ∀ (d Ω e r:ℝ) (s:ℕ),0 ≤ d →
      d ≤ ∏j∈Ico i t,(B j)^2*(B (j+1))^7 → 0 ≤ Ω → Ω ≤ B i → s ≤ a → 0 ≤ e →
      (∀j∈Ico i t, 2 ≤ B j) →
      r ≤ e+∑ j∈Ico i t, ε*(regulatorRun R.family N per (j+2))^q →
      d^3*Ω^s*r ≤ (regulatorRun R.family N per t)^(-η)*(e+ε*(3*regulatorRun R.family N per t)^q) := by
  filter_upwards [WilsonReceivedCloseChainFunding.original R simple degree (3+a) q cap loss ep]
    with t bought
  intro m mt close N per top i mi it d Ω e r s d0 dMax o0 page sz e0 stages rent
  have one (j:ℕ) : 1 ≤ B j := budget_pos R
  let scale := fun j:ℕ=>(B j)^2*(B (j+1))^7
  have scale0 (j:ℕ):0 ≤ scale j := mul_nonneg (pow_nonneg (zero_le_one.trans (one j)) _)
    (pow_nonneg (zero_le_one.trans (one (j+1))) _)
  have paid := bought m mt close N per top.le i mi it.le scale (fun _=>3+a) e e0
    (fun j hj=>⟨stages j hj,scale0 j,le_rfl,le_rfl⟩)
  have rents : r ≤ e+∑ j∈Ico i t,ε*(regulatorRun R.family N per (min N (j+2)))^q :=by
    convert rent using 2
    exact Finset.sum_congr rfl (fun j hj=>by rw [min_eq_right (by
      have jt := (mem_Ico.mp hj).2;omega)])
  have total:0 ≤ e+∑ j∈Ico i t,ε*(regulatorRun R.family N per (min N (j+2)))^q :=
    add_nonneg e0 (sum_nonneg fun j _=>mul_nonneg ep (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _))
  exact (mul_le_mul_of_nonneg_left rents (mul_nonneg (pow_nonneg d0 _) (pow_nonneg o0 _))).trans
    ((mul_le_mul_of_nonneg_right (charge B it one d0 dMax o0 page sz) total).trans paid)

end YM.Integration.WilsonThermometerAncestralPrice
