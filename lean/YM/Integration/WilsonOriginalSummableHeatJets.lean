import YM.Integration.WilsonOriginalTestedFourierBank

/-! Absolute convergence of each derivative of each fixed heat coefficient.
This permits recropping the compact signed comparison after its spatial sums. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSummableHeatJets
open Filter Finset Function Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped Topology BigOperators
open WilsonOriginalIntegerModeCut (size)
open WilsonOriginalFourierLattice (height)
open WilsonOriginalLowFourierJets (cube jet)
open WilsonOriginalTestedFourierBank (Prices)

theorem original {G : Gauge} {d j : ℕ} {warm : ℝ → ℝ} (hG : G.Simple) (paid : Coupling G warm)
    {read : ℝ → (Fin d → ℤ) → ℂ} {coeff : ℕ → (Fin d → ℤ) → ℂ}
    (b : Prices warm read coeff) (e : ℕ) (axis : Fin j → Fin d) (unit : Fin j → ℂ) :
    Summable fun v => ‖jet axis unit v*coeff e v‖ := by
  let M := ∏ i, ‖unit i‖
  have hM : 0 ≤ M := prod_nonneg fun _ _ => norm_nonneg _
  let fee : ℝ := M*2^(2*d)
  have hf : 0 ≤ fee := by dsimp [fee];positivity
  obtain ⟨S,income⟩ := eventually_atTop.mp
    (WilsonOriginalTestedFourierBank.original hG paid b e (12*(j+2*d)) zero_lt_one)
  let T := max 1 S
  have hT : 1 ≤ T := le_max_left _ _
  let N := ⌈T^12⌉₊
  let box := cube d N
  let line := fun v => ‖jet axis unit v*coeff e v‖
  let far := fun v => if v ∈ box then 0 else line v
  have one (v) : far v ≤ fee*(1+(height v:ℝ))⁻¹^(2*d) := by
    by_cases hv : v ∈ box
    · simp only [far,if_pos hv];positivity
    have late : N < height v := lt_of_not_ge fun h => hv ((WilsonOriginalIntegerModeCut.member v N).mpr h)
    have big : T^12 < size v^12 :=
      (Nat.le_ceil _).trans_lt (by rw [WilsonOriginalIntegerModeCut.size_pow];exact_mod_cast late)
    have hs : T < size v := lt_of_not_ge fun h => big.not_ge (pow_le_pow_left₀ (WilsonOriginalIntegerModeCut.nonnegative v) h _)
    have spend := income (size v) ((le_max_right _ _).trans hs.le) v rfl (Fin.last e)
    have high := WilsonOriginalHighModeExpense.spend 0 j (2*d) (hT.trans hs.le) zero_lt_one
      (u:=1) (by simpa only [mul_one] using hT.trans hs.le) (norm_nonneg (coeff e v)) (by simpa using spend)
    have chr : 0 < (1+(height v:ℝ))^(2*d) := by positivity
    have small : (size v^12)^j * ‖coeff e v‖ ≤ 2^(2*d)/(1+(height v:ℝ))^(2*d) :=
      (le_div_iff₀ chr).mpr (by simpa only [WilsonOriginalIntegerModeCut.size_pow,one_pow,mul_one] using high)
    simp only [far,if_neg hv,line,norm_mul]
    calc
      _ ≤ (M*(size v^12)^j)*‖coeff e v‖ := mul_le_mul_of_nonneg_right (WilsonOriginalIntegerModeCut.original axis unit v) (norm_nonneg _)
      _ ≤ M*(2^(2*d)/(1+(height v:ℝ))^(2*d)) := by rw [mul_assoc];exact mul_le_mul_of_nonneg_left small hM
      _ = _ := by simp [fee,div_eq_mul_inv,mul_assoc]
  have major (v) := (one v).trans (mul_le_mul_of_nonneg_left (WilsonOriginalFourierLattice.pays v) hf)
  have farSum : Summable far := Summable.of_nonneg_of_le
    (fun v => by
      by_cases hv : v ∈ box
      · simp [far,hv]
      · simpa only [far,if_neg hv,line] using norm_nonneg (jet axis unit v*coeff e v)) major ((WilsonOriginalFourierLattice.summable d).mul_left fee)
  have nearSum : Summable fun v => if v ∈ box then line v else 0 :=
    summable_of_ne_finset_zero (s:=box) fun v hv => by simp [hv]
  apply (nearSum.add farSum).congr
  intro v
  by_cases hv : v ∈ box <;> simp [hv,far,line]

end YM.Integration.WilsonOriginalSummableHeatJets

