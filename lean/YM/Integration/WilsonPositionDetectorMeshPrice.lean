import YM.Integration.WilsonPositionMeasuredRawPanel

/-! The finite detector price at the first two orders follows directly
from the original Wilson parity and its signed first Wick response. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionDetectorMeshPrice
open Filter Function Set Finset XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2 FVA2.Register
open WilsonPositionRawMesh WilsonPositionRawDetector
open scoped BigOperators Topology Classical
variable {G : Gauge} (Z : WilsonPrescription G) (hG : G.Simple)

theorem even_coefficient (m : Mesh) (hm : Z.store.Meets Z.scheme m 6) (k : ℕ) (even : Even k) :
    PowerSeries.coeff k (Rose.chosen Z.scheme Z.criterion m) = 0 := by
  have h := congrArg (PowerSeries.coeff k) (Rose.odd_c Z.scheme Z.criterion m hm)
  rw [Rose.inversion,PowerSeries.coeff_rescale,map_neg,even.neg_one_pow,one_mul] at h
  linear_combination h/2

include hG in
theorem through_two (q : ℕ) (small : q ≤ 2) :
    ∀ᶠ i : ℕ in atTop, mass Z (Z.run.step i) q ≤ 2 := by
  have h := (Rose.xc Z.scheme Z.criterion hG).comp (goesFront (Expense.Stretched.runs Z.run))
  have k : Tendsto (fun i : ℕ => linear Z (Z.run.step i)) atTop (𝓝 1) :=
    Complex.continuous_re.continuousAt.tendsto.comp h
  have good := (goesFront (Expense.Stretched.runs Z.run)).eventually
    (Z.store.nested_solution Z.scheme 6 Cirrus.frontier).2
  filter_upwards [k.abs.eventually_lt_const (by norm_num : |(1:ℝ)| < 2),good] with i first ready
  have zero := Rose.zero_choice Z.scheme Z.criterion (Z.run.step i)
  have two := even_coefficient Z (Z.run.step i) ready.1 2 (by decide)
  interval_cases q <;>
    simp [mass,detector,Fin.sum_univ_succ,PowerSeries.coeff_zero_eq_constantCoeff_apply,zero]
  · exact first.le
  · rw [two]
    simp only [Complex.zero_re,abs_zero,add_zero]
    exact first.le

include hG in
theorem observed (q : ℕ) (small : q ≤ 2) {l : Filter ℝ} {t : ℝ → ℝ}
    (positive : ∀ᶠ r in l, 0 < t r) (cold : Tendsto t l (𝓝 0)) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ r in l, ∀ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (t r),
      (1+mass Z (Z.run.step i) q)^q*|t r| ≤ ε := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (through_two Z hG q small)
  have paid : Tendsto (fun r => (3:ℝ)^q*|t r|) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=(3:ℝ)^q)).mul cold.abs
  filter_upwards [(WilsonPositionAuxiliaryMesh.grows Z.run q l positive cold).eventually_ge_atTop N,
    paid.eventually_lt_const he] with r enough budget i hi
  have bp : 0 ≤ mass Z (Z.run.step i) q := sum_nonneg fun _ _=>abs_nonneg _
  have price := hN i (enough.trans hi)
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith)
    (by linarith : 1+mass Z (Z.run.step i) q ≤ 3) q) (abs_nonneg _)).trans budget.le

end YM.Integration.WilsonPositionDetectorMeshPrice
