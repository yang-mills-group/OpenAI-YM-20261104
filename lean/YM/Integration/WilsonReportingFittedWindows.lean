import YM.Integration.WilsonReportingRegisteredWindows
import YM.Integration.WilsonReportingFactorySingleton

/-! The actual angular coefficients filed by the original Wilson factory at
the reporting date pay the complete local chart exception. All genuine
later regulators and periods occur after the purchase of the error. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingFittedWindows
open Function Filter Finset MeasureTheory Lattice RG Wilson Source Labels RG12
open PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Pulse RG05Readout.Address RG05Readout.Native
open OPE.Therm WilsonReportingPlaquetteWindows WilsonReportingRegisteredWindows
open scoped Topology Classical BigOperators
variable {G : Gauge} (R : Run G) {V : Type} [Fintype V] [DecidableEq V]

def exceptional (D : V → ℕ) (φ : Wave V) (k N per t : ℕ) (y : (i : V) → R.family.label (D i))
    (r : ℝ) (ξ : Cloud V)
    (cells : placements (V:=V) R.family k per t × rows R D → V → Finset (Face (Per (R.family.side k per))))
    (U : Config G (R.family.side k per)) : ℂ :=
  ∑ a : placements (V:=V) R.family k per t × rows R D,
    (⋃ i, (House.chilly (cells a i) (cool R.family.path.levels k))ᶜ).indicator
      (fun Z => (φ.val (fun i => r⁻¹ • (R.family.S.place (a.1.val i) - ξ i)) *
        price R D k N per y a.2) *
        ∏ i, (R.family.localSection (D i)).places (Pi.single (a.2 i) 1) (a.1.val i) Z) U

private theorem homogeneous (D : V → ℕ) (φ : Wave V) (k N per t : ℕ)
    (y : (i : V) → R.family.label (D i)) (c : V → ℂ) (r : ℝ) (ξ : Cloud V) (cells) (U) :
    exceptional R D φ k N per t (fun i => c i • y i) r ξ cells U =
      (∏ i, c i) * exceptional R D φ k N per t y r ξ cells U := by
  simp only [exceptional,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases good : U ∈ ⋃ i, (House.chilly (cells a i) (cool R.family.path.levels k))ᶜ
  · simp only [Set.indicator_of_mem good,price,Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]; ring
  · simp only [Set.indicator_of_notMem good,mul_zero]

/-- The signed norm bound is homogeneous in all the field coordinates. -/
theorem scaled (stoves : Poetry R.family.path.levels) (simple : G.Simple)
    (D : V → ℕ) (φ : Wave V) (compact : HasCompactSupport φ.val) (d s q : ℕ)
    {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N → ∀ t : ℕ, (t:ℝ) ≤ R.family.path.levels.clock.hatBeta k^s →
      ∀ (y : (i : V) → R.family.label (D i)) r ξ cells,
      (∀ a i, ((cells a i).card:ℝ) ≤ R.family.path.levels.clock.hatBeta k^d) →
      ∫ U, ‖exceptional R D φ k N per t y r ξ cells U‖ ∂scene R.family.path N per k ≤
        (∏ i, (R.family.labels.level (D i)).coeffSize (y i)) *
        (ε * Pert.Asymptotics.regulatorRun R.family N per k^q) := by
  filter_upwards [tested R D stoves simple φ compact d s 0 q ep] with k paid
  intro N per live t width y r ξ cells bound
  let B (i : V) := (R.family.labels.level (D i)).coeffSize (y i)
  let u (i : V) := ((B i:ℂ)⁻¹) • y i
  have positive (i : V) : 0 ≤ B i := Finset.sum_nonneg (fun j _ => norm_nonneg (y i j))
  have each (i : V) (b) : ‖y i b‖ ≤ B i :=
    Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => norm_nonneg (y i j)) (Finset.mem_univ b)
  have normalized (i : V) b : ‖u i b‖ ≤ 1 := by
    change ‖(B i : ℂ)⁻¹ * y i b‖ ≤ 1
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (positive i)]
    by_cases hz : B i = 0
    · simp [hz]
    exact ((mul_le_mul_of_nonneg_left (each i b) (inv_nonneg.mpr (positive i))).trans_eq (inv_mul_cancel₀ hz))
  have restores : y = fun i => (B i : ℂ) • u i := by
    funext i b
    change y i b = (B i:ℂ) * ((B i:ℂ)⁻¹ * y i b)
    by_cases hz : B i = 0
    · have zero : y i b = 0 := norm_le_zero_iff.mp (hz ▸ each i b)
      simp [hz,zero]
    have nonzero : (B i:ℂ) ≠ 0 := by exact_mod_cast hz
    rw [←mul_assoc,mul_inv_cancel₀ nonzero,one_mul]
  have invoice := paid N per live t width u (fun i b => by simpa only [pow_zero] using normalized i b) r ξ cells bound
  change (∫ U, ‖exceptional R D φ k N per t u r ξ cells U‖ ∂scene R.family.path N per k) ≤ _ at invoice
  calc
    _ = (∏ i, B i) * ∫ U, ‖exceptional R D φ k N per t u r ξ cells U‖ ∂scene R.family.path N per k := by
      conv_lhs => rw [restores]
      simp only [homogeneous,norm_mul,norm_prod,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (positive _)]
      exact integral_const_mul ..
    _ ≤ _ := mul_le_mul_of_nonneg_left invoice (Finset.prod_nonneg (fun i _ => positive i))

private theorem coefficient_mass {C : Family G} (hC : C.Makes) {d : ℕ} (t : Letter d)
    (x : C.label (kept t)) (k N per : ℕ) :
    (C.labels.level (kept t)).coeffSize (WilsonReportingFactorySingleton.measured hC t x k N per t) =
      size (C:=C) (WilsonReportingFactorySingleton.measured hC t x k N per) := by
  rw [WilsonReportingFactorySingleton.measured, chunk_self, size_chunk]

/-- The coefficients come from the germ of the submitted physical column.
Only the original input masses and requested accuracy remain. -/
theorem original (stoves : Poetry R.family.path.levels) (simple : G.Simple)
    (D : V → ℕ) (letter : (i : V) → Letter (D i)) (φ : Wave V)
    (compact : HasCompactSupport φ.val) (d s q : ℕ) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N → ∀ t : ℕ, (t:ℝ) ≤ R.family.path.levels.clock.hatBeta k^s →
      (∀ i, R.family.ref (kept (letter i)) ≤ k ∧ R.family.ref (D i) ≤ k) →
      ∀ (x : (i : V) → R.family.label (kept (letter i))) r ξ cells,
      (∀ a i, ((cells a i).card:ℝ) ≤ R.family.path.levels.clock.hatBeta k^d) →
      let y := fun i => (WilsonReportingFactorySingleton.measured (C:=R.family) R.makes (letter i) (x i) k N per) (letter i)
      ∫ U, ‖exceptional R (fun i => kept (letter i)) φ k N per t y r ξ cells U‖ ∂scene R.family.path N per k ≤
        (∏ i, mass R.family (kept (letter i)) (x i)) *
        (ε * Pert.Asymptotics.regulatorRun R.family N per k^q) := by
  let n := Fintype.card V
  have receipt : ∀ᶠ k : ℕ in atTop, ∀ i : V, ∀ {N per : ℕ} (x : R.family.label (kept (letter i))),
      R.family.ref (kept (letter i)) ≤ k → R.family.ref (D i) ≤ k → k ≤ N →
      size (C:=R.family) (WilsonReportingFactorySingleton.measured (C:=R.family) R.makes (letter i) x k N per) ≤
        2 * mass R.family (kept (letter i)) x := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [WilsonReportingFactorySingleton.fitted R.makes simple (D i)] with k h N per x a b c
    exact h (letter i) x a b c
  filter_upwards [receipt, scaled R stoves simple (fun i => kept (letter i)) φ compact d s q
    (div_pos ep (show 0 < (2:ℝ)^n by positivity))] with k fit grant
  intro N per live t width ages x r ξ cells bound y
  have fee (i : V) : (R.family.labels.level (kept (letter i))).coeffSize (y i) ≤
      2 * mass R.family (kept (letter i)) (x i) := by
    exact (coefficient_mass (C:=R.family) R.makes (letter i) (x i) k N per).le.trans
      (fit i (per:=per) (x i) (ages i).1 (ages i).2 live)
  have prod := Finset.prod_le_prod
    (s:=Finset.univ) (fun i _ => (Finset.sum_nonneg (fun b _ => norm_nonneg (y i b)) :
      0 ≤ (R.family.labels.level (kept (letter i))).coeffSize (y i))) (fun i _ => fee i)
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at prod
  have physical := grant N per live t width y r ξ cells bound
  apply physical.trans
  let g := Pert.Asymptotics.regulatorRun R.family N per k
  have gpos : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have positive : 0 ≤ ε/2^n*g^q := mul_nonneg (div_nonneg ep.le (by positivity)) (pow_nonneg gpos _)
  exact (mul_le_mul_of_nonneg_right prod positive).trans_eq (by dsimp only [n,g]; field_simp)

end YM.Integration.WilsonReportingFittedWindows
