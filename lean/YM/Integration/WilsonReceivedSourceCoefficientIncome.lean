import YM.Integration.WilsonReceivedSourceCoefficientBound
import YM.Integration.WilsonReceivedSourceRoster

/-! Coefficientwise, before sampling the coupling, on the funded outgoing marked field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedSourceCoefficientIncome
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise
open Exterior Stationary Comparison.RG02 AllOrder AllOrder.Floe AllOrder.Floe.Step
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {V X ι : Type} [DecidableEq V] {G : Gauge} {n : Side} {P : Passport n V} {Γ : Census V}

def price (G : Gauge) (σ cap : ℝ) (order shelf : ℕ) : ℝ :=
  (max 1 (2*(G.colorScale*cap)/σ))^(order+shelf+1)

variable (M : ι → Row P Γ G X) (w : V → ℝ) (grades : V → ℕ) {σ cost : ℝ} {order count shelf : ℕ}
  (estate : Scene.Armada M w grades σ cost order count shelf) (hs : 0 < σ)
  (x : X) (A : Link G n) {cap : ℝ} (hc : 0 ≤ cap) (axis : ∀ e, ‖collect G (arm G n 1 A) e‖ ≤ cap)
  (j : ℕ) (hj : j ≤ order)
include estate hs hc axis hj

private theorem entry (i : ι) :
    ‖(M i).paint x * ((M i).markReceipt j A : ℂ)‖ ≤ (M i).salary * price G σ cap order shelf := by
  have rank := Scene.Armada.degreeR grades estate.toMinistry (M i) (estate.purchases.usable i)
  have bound := WilsonReceivedSourceCoefficientBound.row (M i) x A hs hc axis
    (estate.honor i) (estate.purchases.spend i) j
  let a := 2*(G.colorScale*cap)/σ
  have a0 : 0 ≤ a := div_nonneg (mul_nonneg (by norm_num) (mul_nonneg G.colorScale_pos.le hc)) hs.le
  have crest := (M i).lamp.crest
  have degree : j-(M i).lamp.e+(M i).lamp.r ≤ order+shelf+1 := by omega
  have powers : a^(j-(M i).lamp.e+(M i).lamp.r) ≤ (max 1 a)^(order+shelf+1) :=
    (pow_le_pow_left₀ a0 (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) degree)
  exact bound.trans (mul_le_mul_of_nonneg_left powers (M i).sound.le)

/-- Absolute income of the actual occupied Laurent row before summing its signs. -/
theorem wallet (s : Γ.Mode) :
    SumBudget (fun i => Poly.toll w s * ‖if (M i).mode=s then
      (M i).paint x * ((M i).markReceipt j A : ℂ) else 0‖)
      (price G σ cap order shelf * ((s.val.image P.origin).card*cost)) := by
  have non : 0 ≤ price G σ cap order shelf := by unfold price; positivity
  have pay := WilsonFirstReceivedIssuedIncome.salary M w estate.positive hs.le estate.suggests s
  refine Push.PriceCompiler.sumBudget_mono (Push.Local.sumBudget_mul_left pay non) ?_ ?_ le_rfl
  · intro i; exact mul_nonneg (Poly.worth estate.positive _).le (norm_nonneg _)
  · intro i
    by_cases h : (M i).mode=s
    · simp only [if_pos h]
      refine (mul_le_mul_of_nonneg_left (entry M w grades estate hs x A hc axis j hj i)
        (Poly.worth estate.positive s).le).trans_eq ?_
      ring
    · simp [h]

/-- The paid finite program's true tested coefficient for every occupied face. The count is
the number of its distinct marked origins on its torus. -/
theorem original (layout : Layout G) (tape : Finset Age) (s : Γ.Mode) :
    let issued := Air.craft M (fun i => (M i).paint x) grades layout tape
    Poly.toll w s * ‖(Air.discharge issued j (arm G n 1 A)).part s‖ ≤
      price G σ cap order shelf * ((s.val.image P.origin).card*cost) := by
  intro issued
  letI : Fintype V := Fintype.ofInjective Γ.fire (fun a b h => (Γ.fire_inj a b).mp h)
  let κ := Poly.toll w s
  let ink (i : ι) := (M i).paint x
  let roster := Air.license M ink grades w estate hs (fun i => estate.honor i x)
  let fj (i : ι) := if (M i).mode=s then ink i * ((M i).markReceipt j A : ℂ) else 0
  have readings : HasSum fj ((Air.discharge issued j (arm G n 1 A)).part s) := by
    apply (Pi.hasSum.mp (Air.compared M ink grades roster layout tape A j) s).congr_fun
    intro i
    change fj i = (Poly.send (M i).mode _).part s
    rw [Poly.part_send]
    by_cases h : (M i).mode=s <;> simp [fj,h,eq_comm]
  have live : 0 < κ := Poly.worth estate.positive s
  have income := wallet M w grades estate hs x A hc axis j hj s
  have summable : Summable fun i => ‖fj i‖ := by
    simpa only [←mul_assoc,inv_mul_cancel₀ live.ne',one_mul,κ,fj,ink] using (income.2.1.mul_left κ⁻¹)
  rw [← readings.tsum_eq]
  calc
    _ ≤ κ*(∑' i, ‖fj i‖) := mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm summable) live.le
    _ = ∑' i, κ*‖fj i‖ := tsum_mul_left.symm
    _ ≤ _ := income.2.2

end YM.Integration.WilsonReceivedSourceCoefficientIncome
