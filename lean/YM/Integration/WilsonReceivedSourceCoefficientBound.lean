import YM.Integration.WilsonReceivedSourceRowJet

/-! Laurent coefficients of the issued physical curvature words, on the genuine rooted ray. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedSourceCoefficientBound
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise
open Exterior Stationary Comparison.RG02 WilsonMeasuredPathTaylor FundedCurvatureRayTaylor
open WilsonFirstReceivedIssuedRowTaylor
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {V X : Type} [DecidableEq V] {G : Gauge} {n : Side} {P : Passport n V} {R : Census V}

private theorem ray (A : Link G n) (t : ℝ) :
    Stationary.input G n (t • A) =
      field (collect G (arm G n 1 A)) t := by
  rw [Stationary.input, map_smul]
  simpa only [Comparison.RG02.Integral.sample, one_smul, one_mul] using
    WilsonFirstReceivedIssuedRowTaylor.sample (arm G n 1 A) 1 t

private theorem paidLength {r : ℕ} (a : Atom G r) {σ D : ℝ}
    (hs : 0 < σ) (hd : 0 ≤ D) (budget : a.budget σ ≤ 1) (k : ℕ) :
    a.magnitude * ((2*(a.length:ℝ)*D)^k/k.factorial) ≤ (2*D/σ)^k := by
  have hm : 0 ≤ a.magnitude := sum_nonneg fun _ _ => abs_nonneg _
  have split : 2*(a.length:ℝ)*D = (2*D/σ)*(σ*a.length) := by field_simp
  have hx := Real.pow_div_factorial_le_exp (σ*a.length) (by positivity) k
  rw [split,mul_pow]
  calc
    _ = (2*D/σ)^k * (a.magnitude * ((σ*a.length)^k/k.factorial)) := by ring
    _ ≤ (2*D/σ)^k * (a.magnitude * Real.exp (σ*a.length)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hm) (by positivity)
    _ ≤ _ := mul_le_of_le_one_right (by positivity) budget

/-- The genuine finite color sum spends the atom's length wallet at the requested radial order. -/
theorem radial (T : Row P R G X) (x : X) (A : Link G n) {σ cap : ℝ} (hs : 0 < σ)
    (hc : 0 ≤ cap) (axis : ∀ e, ‖collect G (arm G n 1 A) e‖ ≤ cap)
    (paid : T.Budget) (budget : T.Graceful σ) (k : ℕ) :
    ‖T.paint x * (PertExtension.Series.Radial.jet (Helmet.frame T.atom T.center) k A : ℝ)‖ ≤
      T.salary * (2*(G.colorScale*cap)/σ)^k := by
  classical
  let v := collect G (arm G n 1 A)
  let D := G.colorScale*cap
  have hd : 0 ≤ D := mul_nonneg G.colorScale_pos.le hc
  have avail : Available T.atom T.center v D := by
    intro _ e _
    rw [speed,G.colorMat_norm]
    exact mul_le_mul_of_nonneg_left (axis e) G.colorScale_pos.le
  let word b := read v T.center (letters T.atom b)
  let coef b := T.paint x * (T.atom.coeff b : ℂ)
  have regular b : ContDiffAt ℝ k (word b) 0 := ((read_smooth ..).of_le le_top).contDiffAt
  have physical : (fun t : ℝ => T.nominal 1 x (Stationary.input G n (t • A))) =
      fun t => ∑ b, coef b * word b t := by
    funext t
    simp only [Row.nominal,Row.grain,one_zpow,one_mul,Pi.smul_apply,smul_eq_mul,ray,
      FundedCurvatureRayTaylor.evaluated,mul_sum,v,word,coef,mul_assoc]
  have derived : iteratedDeriv k (fun t => ∑ b, coef b * word b t) 0 =
      ∑ b, coef b * iteratedDeriv k (word b) 0 := by
    rw [iteratedDeriv_fun_sum (fun b _ => contDiffAt_const.mul (regular b))]
    apply sum_congr rfl
    intro b _
    exact iteratedDeriv_const_smul (regular b) (coef b)
  have perWord b : ‖iteratedDeriv k (word b) 0‖ ≤ (2*(T.atom.length:ℝ)*D)^k := by
    have h := FundedCurvatureRayTaylor.priced T.atom T.center v hd avail b
    exact (product v T.center (letters T.atom b) 0 k).trans (pow_le_pow_left₀ h.1 h.2 k)
  have total : ‖∑ b, coef b * iteratedDeriv k (word b) 0‖ ≤
      (‖T.paint x‖ * T.atom.magnitude) * (2*(T.atom.length:ℝ)*D)^k := by
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ b, (‖T.paint x‖ * |T.atom.coeff b|) * (2*(T.atom.length:ℝ)*D)^k := by
        apply sum_le_sum
        intro b _
        rw [norm_mul, show ‖coef b‖ = ‖T.paint x‖ * |T.atom.coeff b| by
          simp only [coef,norm_mul,Complex.norm_real,Real.norm_eq_abs]]
        exact mul_le_mul_of_nonneg_left (perWord b) (by positivity)
      _ = _ := by rw [←sum_mul,←mul_sum]; rfl
  rw [← WilsonPhysicalMarkedDefect.RowCoefficients.coefficient T x k A, physical,derived,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (k.factorial:ℝ)⁻¹ by positivity)]
  calc
    _ ≤ (k.factorial:ℝ)⁻¹ * ((‖T.paint x‖ * T.atom.magnitude) * (2*(T.atom.length:ℝ)*D)^k) :=
      mul_le_mul_of_nonneg_left total (by positivity)
    _ = ‖T.paint x‖ * (T.atom.magnitude * ((2*(T.atom.length:ℝ)*D)^k/k.factorial)) := by ring
    _ ≤ _ := mul_le_mul (paid x) (paidLength T.atom hs hd budget k)
      (mul_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)) T.sound.le

/-- Rows below birth vanish. Each surviving Laurent row retains its actual field degree. -/
theorem row (T : Row P R G X) (x : X) (A : Link G n) {σ cap : ℝ} (hs : 0 < σ)
    (hc : 0 ≤ cap) (axis : ∀ e, ‖collect G (arm G n 1 A) e‖ ≤ cap)
    (paid : T.Budget) (budget : T.Graceful σ) (j : ℕ) :
    ‖T.paint x * (T.markReceipt j A : ℂ)‖ ≤
      T.salary * (2*(G.colorScale*cap)/σ)^(j-T.lamp.e+T.lamp.r) := by
  by_cases h : T.lamp.e ≤ j
  · simpa only [Row.markReceipt,if_pos h] using radial T x A hs hc axis paid budget (j-T.lamp.e+T.lamp.r)
  · simp only [Row.markReceipt,if_neg h,Complex.ofReal_zero,mul_zero,norm_zero]
    exact mul_nonneg T.sound.le (pow_nonneg (div_nonneg (mul_nonneg (by positivity)
      (mul_nonneg G.colorScale_pos.le hc)) hs.le) _)
end YM.Integration.WilsonReceivedSourceCoefficientBound
