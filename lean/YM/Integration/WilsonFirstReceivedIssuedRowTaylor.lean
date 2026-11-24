import YM.Integration.FundedCurvatureRayTaylor
import YM.QuadraticLocal.Earn.Rendering
import YM.Comparison.RG02.Integral.Bill

/-! The Taylor error of an issued marked row on the real group-field ray.
The loan's own rank bound pays its Laurent pole before the rows are summed. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFirstReceivedIssuedRowTaylor
open Lattice Wilson RG Marker Ac Exterior QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn
open WilsonMeasuredPathTaylor FundedCurvatureRayTaylor
open scoped BigOperators Classical Matrix.Norms.Frobenius

variable {V α : Type*} [DecidableEq V] {G : Gauge} {n : Side}
variable {P : Passport n V} {R : Census V}

def approximation (T : Row P R G α) (g : ℝ) (u : α) (v : Directions G n)
    (d : ℕ) (t : ℝ) : ℂ :=
  T.paint u * (g ^ T.lamp.lag : ℝ) * polynomial T.atom T.center v d t

def column (T : Row P R G α) (g : ℝ) (u : α) (v : Directions G n) (d : ℕ) : Polynomial ℂ :=
  ∑ b : Fin T.lamp.r → G.ColorIndex, ∑ j ∈ Finset.range (d + 1), Polynomial.monomial j
    (T.paint u * (g ^ T.lamp.lag : ℝ) * T.atom.coeff b *
      ((j.factorial : ℝ)⁻¹ * g ^ j : ℝ) *
      iteratedDeriv j (read v T.center (letters T.atom b)) 0)

theorem degree (T : Row P R G α) (g : ℝ) (u : α) (v : Directions G n) (d : ℕ) :
    (column T g u v d).natDegree ≤ d := by
  unfold column
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro b _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_monomial_le ..).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem evaluated (T : Row P R G α) (g : ℝ) (u : α) (v : Directions G n) (d : ℕ) (z : ℝ) :
    (column T g u v d).eval (z : ℂ) = approximation T g u v d (g * z) := by
  unfold column approximation polynomial jet
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_pow, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem original (T : Row P R G α) (paid : T.Budget) (g : ℝ) (u : α)
    (v : Directions G n) {A : ℝ} (ha : 0 ≤ A) (available : Available T.atom T.center v A)
    (d : ℕ) (t : ℝ) :
    ‖T.nominal g u (field v t) - approximation T g u v d t‖ ≤
      T.salary * |g ^ T.lamp.lag| * (T.atom.magnitude * bill T.atom.length A d t) := by
  have factored : T.nominal g u (field v t) - approximation T g u v d t =
      (T.paint u * (g ^ T.lamp.lag : ℝ)) *
        ((T.atom.unmasked (field v t) T.center : ℂ) - polynomial T.atom T.center v d t) := by
    change T.paint u * ((g ^ T.lamp.lag * T.atom.unmasked (field v t) T.center : ℝ) : ℂ) -
      _ = _
    rw [Complex.ofReal_mul]
    unfold approximation
    ring
  rw [factored, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (mul_le_mul_of_nonneg_right (paid u) (abs_nonneg _))
    (FundedCurvatureRayTaylor.original T.atom T.center v ha available d t)
    (norm_nonneg _) (mul_nonneg T.sound.le (abs_nonneg _))

private theorem loan_power (l : Loan) {g : ℝ} (hg : 0 < g) (hu : g ≤ 1) (q : ℕ) :
    |g ^ l.lag| * g ^ (q + l.toll + 1) ≤ g ^ q := by
  have stamp : g ^ l.lag * g ^ (l.toll + 1) = g ^ l.stamp := by
    rw [← zpow_natCast, ← zpow_add₀ hg.ne', ← zpow_natCast, l.stamped]
    congr 1
    simp [Loan.power, add_comm]
  rw [abs_of_pos (zpow_pos hg _), show q + l.toll + 1 = (l.toll + 1) + q by omega,
    pow_add, ← mul_assoc, stamp]
  exact mul_le_of_le_one_left (pow_nonneg hg.le _) (pow_le_one₀ hg.le hu)

theorem bounded (T : Row P R G α) (paid : T.Budget) {g : ℝ} (hg : 0 < g) (hu : g ≤ 1)
    (u : α) (v : Directions G n) {A : ℝ} (ha : 0 ≤ A) (available : Available T.atom T.center v A)
    (q : ℕ) (z : ℝ) :
    ‖T.nominal g u (field v (g * z)) - approximation T g u v (q + T.lamp.toll) (g * z)‖ ≤
      T.salary * T.atom.magnitude * bill T.atom.length A (q + T.lamp.toll) z * g ^ q := by
  have bp : bill T.atom.length A (q + T.lamp.toll) (g * z) =
      g ^ (q + T.lamp.toll + 1) * bill T.atom.length A (q + T.lamp.toll) z := by
    simp only [bill, abs_mul, abs_of_pos hg, mul_pow]
    ring
  apply (original T paid g u v ha available _ _).trans
  rw [bp]
  have pos : 0 ≤ T.salary * T.atom.magnitude * bill T.atom.length A (q + T.lamp.toll) z := by
    have hs := T.sound
    have hm : 0 ≤ T.atom.magnitude := Finset.sum_nonneg fun _ _ => abs_nonneg _
    unfold bill
    positivity
  calc
    _ = (T.salary * T.atom.magnitude * bill T.atom.length A (q + T.lamp.toll) z) *
        (|g ^ T.lamp.lag| * g ^ (q + T.lamp.toll + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (loan_power T.lamp hg hu q) pos

theorem sample (a : fieldDir G n 1) (g z : ℝ) :
    Comparison.RG02.Integral.sample g (z • a) = field (collect G a) (g * z) := by
  rw [Comparison.RG02.Integral.sample, smul_smul]
  funext e
  change G.lieExp ((g * z) • a (e.1, coord e.2)) * (1 : G.El) =
    G.lieExp ((g * z) • a (e.1, coord e.2))
  exact mul_one _

private theorem curvature_bill {k : ℕ} (atom : Atom G k) {σ A : ℝ} (hs : 0 < σ)
    (ha : 0 ≤ A) (rich : atom.budget σ ≤ 1) (d : ℕ) (z : ℝ) :
    atom.magnitude * bill atom.length A d z ≤ (2 * A * |z| / σ) ^ (d + 1) := by
  have mag : 0 ≤ atom.magnitude := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have pos : 0 ≤ (2 * A * |z| / σ) ^ (d + 1) := by positivity
  have scaled : 2 * (atom.length : ℝ) * A * |z| =
      (2 * A * |z| / σ) * (σ * atom.length) := by field_simp
  have split : bill atom.length A d z = (2 * A * |z| / σ) ^ (d + 1) *
      ((σ * atom.length) ^ (d + 1) / (d + 1).factorial) := by
    rw [bill, ← mul_pow, ← mul_div_assoc, ← mul_pow, scaled]
  have expo := Real.pow_div_factorial_le_exp (σ * atom.length) (by positivity) (d + 1)
  rw [split]
  calc
    _ = (2 * A * |z| / σ) ^ (d + 1) *
        (atom.magnitude * ((σ * atom.length) ^ (d + 1) / (d + 1).factorial)) := by ring
    _ ≤ (2 * A * |z| / σ) ^ (d + 1) * (atom.magnitude * Real.exp (σ * atom.length)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left expo mag) pos
    _ ≤ _ := mul_le_of_le_one_right pos rich

/-- On the actual independently prescribed physical probe, the funded
stencil width pays the complete path length. The source salary is unweighted
in the coupling. -/
theorem filed (T : Row P R G α) (paid : T.Budget) {σ : ℝ} (hs : 0 < σ)
    (rich : T.Graceful σ) {g : ℝ} (hg : 0 < g) (hu : g ≤ 1) (u : α)
    (a : fieldDir G n 1) {A : ℝ} (ha : 0 ≤ A) (axis : ∀ e, ‖collect G a e‖ ≤ A)
    (q : ℕ) (z : ℝ) :
    ‖T.nominal g u (Comparison.RG02.Integral.sample g (z • a)) -
        approximation T g u (collect G a) (q + T.lamp.toll) (g * z)‖ ≤
      T.salary * (2 * (G.colorScale * A) * |z| / σ) ^ (q + T.lamp.toll + 1) * g ^ q := by
  rw [sample]
  have ha' := mul_nonneg G.colorScale_pos.le ha
  have available : Available T.atom T.center (collect G a) (G.colorScale * A) := by
    intro _ e _
    rw [speed, G.colorMat_norm]
    exact mul_le_mul_of_nonneg_left (axis e) G.colorScale_pos.le
  refine (bounded T paid hg hu u _ ha' available q z).trans ?_
  rw [mul_assoc T.salary T.atom.magnitude]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (curvature_bill T.atom hs ha' rich _ z) T.sound.le) (pow_nonneg hg.le _)

end YM.Integration.WilsonFirstReceivedIssuedRowTaylor
