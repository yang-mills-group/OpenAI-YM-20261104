import YM.Integration.WilsonOriginalTestedFourierBank

/-! The high-frequency signed difference at one physical radius.
Its coefficients are the same ones as in the higher-order sample bank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedHighModes
open Filter Finset Function Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped Topology BigOperators
open WilsonOriginalIntegerModeCut (size)
open WilsonOriginalTestedFourierBank (Prices)

theorem original {G : Gauge} {d : ℕ} {warm : ℝ → ℝ} (hG : G.Simple) (paid : Coupling G warm)
    {read : ℝ → (Fin d → ℤ) → ℂ} {coeff : ℕ → (Fin d → ℤ) → ℂ}
    (b : Prices warm read coeff) (Q j p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ᶠ r : ℝ in trail, ∀ v, let s := size v; let u := warm r
      S ≤ s → 0 < u → u ≤ 1 → 1 ≤ s*u →
      (s^12)^j*‖read r v-∑ e : Fin (Q+1), (u:ℂ)^e.val*coeff e.val v‖*(1+s^12)^(2*d)
      ≤ (2:ℝ)^(2*d)*((Q:ℝ)+2)*ε*u^p := by
  let k := p+12*(j+2*d)
  have bank := WilsonOriginalTestedFourierBank.original hG paid b Q k hε
  have trueField := WilsonOriginalHighModeExpense.original p j d b.A b.D b.c
    b.prefactor b.growth b.width hε
  obtain ⟨S,hS⟩ := eventually_atTop.mp (bank.and trueField)
  refine ⟨max 1 S,le_max_left _ _,?_⟩
  filter_upwards [b.analytic] with r actual v s u large hu hu1 high
  have hs : 1 ≤ s := (le_max_left _ _).trans large
  obtain ⟨smooth,ext⟩ := hS s ((le_max_right _ _).trans large)
  let f := (s^12)^j
  let m := (1+s^12)^(2*d)
  let cost := (2:ℝ)^(2*d)*ε*u^p
  have positive := zero_le_one.trans hs
  have hf : 0 ≤ f := by dsimp [f];positivity
  have hm : 0 ≤ m := by dsimp [m];positivity
  have continuum : f*‖read r v‖*m ≤ cost := calc
    _ ≤ f*(b.A*(u⁻¹)^2*Real.exp (b.D*(u⁻¹)^4-b.c*s^6*u))*m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (actual v) hf) hm
    _ ≤ _ := ext u hu high
  have one (e : Fin (Q+1)) : f*‖(u:ℂ)^e.val*coeff e.val v‖*m ≤ cost := by
    have scalar : ‖(u:ℂ)^e.val*coeff e.val v‖ ≤ ‖coeff e.val v‖ := by
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hu.le hu1)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left scalar hf) hm).trans
      (WilsonOriginalHighModeExpense.spend p j (2*d) hs hu high (norm_nonneg _) (smooth v rfl e))
  have total := norm_sum_le (Finset.univ : Finset (Fin (Q+1))) (fun e => (u:ℂ)^e.val*coeff e.val v)
  calc
    _ ≤ f*(‖read r v‖+∑ e : Fin (Q+1), ‖(u:ℂ)^e.val*coeff e.val v‖)*m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        ((norm_sub_le _ _).trans (add_le_add le_rfl total)) hf) hm
    _ = f*‖read r v‖*m+∑ e : Fin (Q+1), f*‖(u:ℂ)^e.val*coeff e.val v‖*m := by
      rw [mul_add,add_mul,Finset.mul_sum,Finset.sum_mul]
    _ ≤ cost+∑ _ : Fin (Q+1), cost := add_le_add continuum (sum_le_sum fun e _ => one e)
    _ = _ := by simp [cost];ring

end YM.Integration.WilsonOriginalSignedHighModes

