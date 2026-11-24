import YM.Comparison.RG02.Bare.View
import YM.Comparison.RG02.Adjacent.Actual

/-! The centered logarithm of the full finite Wilson push has the native signed
vacuum-action coefficients. The varying coupling enters both the original
Wilson density and its block kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeWilsonBlockExpansion

open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Tree Exterior Marker Multi
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Integral Comparison.RG02.Actual
open Comparison.RG02.Laplace PertExtension.Series PertExtension.Series.Tested
open scoped Classical Topology BigOperators

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
  {O : ChartRatio G} (K : Bulk.Kernel S p P O) (F : Forest S.ratio)
  {V : Type} [DecidableEq V] [Fintype V] {H : Census V} (W : Bulk.Colors H G f)
  (t : S.Choices) (x : fieldDir G c 1) (r : ℕ)

def density (S : StepData c f) (x : fieldDir G c 1) (g : ℝ) : ℝ :=
  S.push (Integral.temperature g) (Wilson.bare (Integral.temperature g)) (Integral.sample g x)

private theorem evaluate (g : ℝ) :
    peval (fun k => Symmetry.Orbit.ground K F t W r k x) r g =
      peval (Laplace.detail (Order.logVac (Bulk.Fk K F t W x r)) H.quiet) r g + Symmetry.price K F t x := by
  simp only [peval, Zone.eval, Symmetry.Orbit.ground, Complex.real_smul, mul_add, sum_add_distrib,
    mul_ite, mul_zero, sum_ite_eq']
  simp

private theorem office_ratio (g : ℝ) :
    Integral.office K F t g 0 x = Integral.office K F t g 0 0 * Real.exp (Symmetry.price K F t x).re := by
  have hz : Bulk.infrared S p P F t (K.b F) 0 = 0 := by
    have h := Symmetry.Pole.price_zero K F t
    simpa only [Symmetry.price,neg_eq_zero,Complex.ofReal_eq_zero] using h
  simp only [Integral.office,Integral.standard,Integral.calorie,hz,sub_zero,zero_sub,
    Real.exp_zero,mul_one,Symmetry.price,Complex.neg_re,Complex.ofReal_re]
  ring

private theorem factor (g : ℝ) (hg : 0 < g) :
    Complex.ofReal (Real.log (density S x g)) =
      Complex.ofReal (Real.log (Integral.office K F t g 0 0)) +
      (Complex.ofReal (Real.log (Bare.rho K F t x g)) + Symmetry.price K F t x) := by
  have h₀ := Integral.office_pos K F t g 0 0 hg
  have hx := Integral.office_pos K F t g 0 x hg
  have hρ := Bare.rho_pos K F t x g hg
  have h : density S x g = Integral.office K F t g 0 x * Bare.rho K F t x g := by
    unfold Bare.rho density
    rw [mul_inv_cancel_left₀ hx.ne']
  rw [h, Real.log_mul hx.ne' hρ.ne', office_ratio K F t x g,
    Real.log_mul h₀.ne' (Real.exp_pos _).ne', Real.log_exp]
  simp only [Complex.ofReal_add, Symmetry.price, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_neg]
  abel

variable (D : BudgetPoint) (hW : Bare.Witnessed W K)
include D hW

private theorem uncentered : Laplace.Trial (fun k => Symmetry.Orbit.ground K F t W r k x)
    (fun g => Complex.ofReal (Real.log (Bare.rho K F t x g)) + Symmetry.price K F t x) r := by
  have h := (Bare.wilson_step_test K F W t x r D hW).2.1
  apply Laplace.bill_congr _ h
  exact Eventually.of_forall fun g => by
    change Complex.ofReal _ - peval _ r g = (Complex.ofReal _ + _) - peval _ r g
    rw [evaluate]
    abel

/-- All first-block vacuum coefficients through the requested horizon are
obtained from the centered logarithm of the literal unmasked nonlinear
Wilson push on every fixed finite lattice and spatial field. -/
theorem centered : Laplace.Trial
    (fun k => Symmetry.Orbit.ground K F t W r k x - Symmetry.Orbit.ground K F t W r k 0)
    (fun g => Complex.ofReal (Real.log (density S x g)) - Complex.ofReal (Real.log (density (G := G) S 0 g))) r := by
  have h := Laplace.trial_add (uncentered K F W t x r D hW)
    (Laplace.trial_scale (-1) (uncentered K F W t 0 r D hW))
  have h₁ : Laplace.Trial (fun k => Symmetry.Orbit.ground K F t W r k x - Symmetry.Orbit.ground K F t W r k 0)
      (fun g => (Complex.ofReal (Real.log (Bare.rho K F t x g)) + Symmetry.price K F t x) -
        (Complex.ofReal (Real.log (Bare.rho K F t 0 g)) + Symmetry.price K F t 0)) r := by
    convert h using 1 <;> funext k <;>
      simp only [Pi.add_apply,Pi.neg_apply,neg_one_smul,sub_eq_add_neg]
  apply Laplace.bill_congr _ h₁
  filter_upwards [eventually_pos] with g hg
  simp only [Pi.sub_apply, factor K F t x g hg, factor K F t 0 g hg]
  abel

end YM.Integration.NativeWilsonBlockExpansion
end
