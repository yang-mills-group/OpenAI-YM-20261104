import YM.MS.Wilson.Energy
import YM.PCalc.Chart
import YM.Extra.WILSON_STARTUP.Face
import Mathlib.Analysis.Analytic.Order

/-! The physical Wilson ultraviolet action on a field ray. Dividing out the
double zero retains the full Wilson functional at every nonzero coupling
and identifies each Taylor coefficient orders two apart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonGerm

open Filter Lattice Wilson RG Exterior MS.Native
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {n : Side}

def ray (B : fieldDir G n 1) (t : ℝ) := Precision.represent (t • B)
def action (B : fieldDir G n 1) (t : ℝ) := Wilson.energy (ray B t)

theorem chart (B : fieldDir G n 1) (t : ℝ) :
    action B t = -Chart.rent (Chart.drive n) (t • collect G B) := by
  have hr : ray B t = Chart.nation (t • collect G B) := by
    funext e
    change G.lieExp (t • B (e.1, coord e.2)) * 1 = G.lieExp (t • B (e.1,coord e.2))
    exact mul_one _
  rw [action,hr,Chart.original_W,neg_neg]

theorem analytic (B : fieldDir G n 1) : AnalyticAt ℝ (action B) 0 := by
  have hc : ContDiffAt ℝ ω (Chart.rent (G := G) (Chart.drive n))
      ((0:ℝ) • collect G B) := by simpa using Chart.rent_s (G := G) (Chart.drive n)
  have hl : ContDiffAt ℝ ω (fun t : ℝ => t • collect G B) 0 := by fun_prop
  rw [funext (chart B)]
  exact (hc.comp 0 hl).neg.analyticAt

theorem zero (B : fieldDir G n 1) : action B 0 = 0 := by
  have hr : ray B 0 = 1 := by
    funext e
    simp [ray, Precision.represent, increment, collect]
  rw [action,hr]
  simp [Wilson.energy,WilsonStartup.face_one]

theorem slope (B : fieldDir G n 1) : deriv (action B) 0 = 0 := by
  apply IsLocalMin.deriv_eq_zero
  filter_upwards with t
  rw [zero]
  exact Wilson.energy_nonneg _

structure Curve (B : fieldDir G n 1) where
  value : ℝ → ℝ
  analytic : AnalyticAt ℝ value 0
  factor t : action B t = t ^ 2 * value t

theorem purchase (B : fieldDir G n 1) : Nonempty (Curve B) := by
  obtain ⟨F,hF,h⟩ := (analytic B).exists_eq_sum_add_pow_mul 2
  refine ⟨⟨F,hF,fun t => ?_⟩⟩
  simpa [Finset.sum_range_succ, zero, slope, smul_eq_mul] using h t

/-- The entire inverse-coupling correction in the original Wilson action. -/
def corrected {B : fieldDir G n 1} (C : Curve B) (P : ℝ → ℝ) (t : ℝ) : ℝ :=
  C.value t + P t * action B t

theorem exact_bare {B : fieldDir G n 1} (C : Curve B) (P : ℝ → ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    bare ((t^2)⁻¹ + P t) (ray B t) = Real.exp (-corrected C P t) := by
  unfold bare corrected
  change Real.exp (-((t^2)⁻¹ + P t) * action B t) = _
  congr 1
  rw [C.factor t]
  field_simp

theorem corrected_analytic {B : fieldDir G n 1} (C : Curve B) {P : ℝ → ℝ}
    (hP : AnalyticAt ℝ P 0) : AnalyticAt ℝ (corrected C P) 0 :=
  C.analytic.fun_add (hP.fun_mul (analytic B))

/-- Normalized physical Taylor coefficients, including their shift from
the inverse square coupling. No order truncation enters this equality. -/
theorem coefficient {B : fieldDir G n 1} (C : Curve B) (k : ℕ) :
    iteratedDeriv k C.value 0 / (k.factorial:ℝ) =
      iteratedDeriv (k+2) (action B) 0 / ((k+2).factorial:ℝ) := by
  have hc : ContDiffAt ℝ (k+2 : ℕ) C.value 0 := C.analytic.contDiffAt
  have hp : ContDiffAt ℝ (k+2 : ℕ) (fun t : ℝ => t^2) 0 := by fun_prop
  rw [funext C.factor, iteratedDeriv_fun_mul hp hc, Finset.sum_eq_single 2]
  · rw [iteratedDeriv_fun_pow_zero, if_pos rfl, Nat.add_sub_cancel]
    have he : (((k + 2).choose 2 : ℕ) : ℝ) * ((2:ℕ).factorial : ℝ) *
        (k.factorial : ℝ) = ((k+2).factorial : ℝ) := by
      exact_mod_cast (by simpa using
        (Nat.choose_mul_factorial_mul_factorial (n:=k+2) (k:=2) (by omega)))
    rw [div_eq_div_iff (by positivity) (by positivity), ← he]
    ring
  · intro i hi hne
    rw [iteratedDeriv_fun_pow_zero,if_neg hne]
    ring
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

end YM.Integration.WilsonLimitConstruction.FundedWilsonGerm
end
