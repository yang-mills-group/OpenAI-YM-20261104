import YM.WilsonCoeffUV.Series.Components.GermJet
import YM.PertExtension.Uniform

/-! Evaluate a formal Wilson jet in an actual radial direction. The
real univariate power series keeps the numerical factorial and every
quadratic clearing factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalRadialSeries
open Function Filter PowerSeries WilsonCoeffUV.Blue
open scoped Classical Topology ContDiff

variable {V : Type} [Fintype V]

def observed (v : Lawn V) : Ink V →+* PowerSeries ℝ := PowerSeries.map (MvPolynomial.eval v)

def scalar (f : ℝ → ℝ) := observed (1 : Lawn Unit) (jet (fun v => f (v ())))

private theorem liftGreen {f : ℝ → ℝ} (h : ContDiffAt ℝ ω f 0) : Green (fun v : Lawn Unit => f (v ())) :=
  h.comp 0 (by fun_prop)

theorem numeric (f : ℝ → ℝ) (h : ContDiffAt ℝ ω f 0) (i : ℕ) :
    coeff i (scalar f) = (i.factorial:ℝ)⁻¹ * iteratedDeriv i f 0 := by
  rw [scalar,observed,coeff_map,rayon]
  have ray := PertExtension.Series.Radial.homogeneous_derivative (fun v : Lawn Unit => f (v ()))
    (1:Lawn Unit) i ((liftGreen h).of_le le_top)
  simpa only [PertExtension.Series.Radial.jet,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one] using ray

theorem restriction (v : Lawn V) (f : Lawn V → ℝ) (h : Green f) :
    observed v (jet f) = scalar (fun t : ℝ => f (t • v)) := by
  have hn : ContDiffAt ℝ ω (fun t : ℝ => f (t • v)) 0 :=
    (show ContDiffAt ℝ ω f ((0:ℝ) • v) by simpa).comp 0 (by fun_prop)
  ext i
  rw [numeric _ hn,observed,coeff_map,rayon]
  exact PertExtension.Series.Radial.homogeneous_derivative f v i (h.of_le le_top)

theorem «local» {f g : ℝ → ℝ} (h : f =ᶠ[𝓝 0] g) : scalar f = scalar g := by
  unfold scalar
  apply congrArg (observed (1:Lawn Unit))
  have atZero : Tendsto (fun z : Lawn Unit=>z ()) (𝓝 0) (𝓝 0) :=
    (continuous_apply ()).tendsto (0:Lawn Unit)
  exact jet_congr (h.comp_tendsto atZero)

@[simp] theorem «variable» : scalar (id : ℝ → ℝ) = X := by
  change observed (1:Lawn Unit) (jet (fun v : Lawn Unit => v ())) = X
  rw [jet_arg]; simp [observed,path]

theorem mul {f g : ℝ → ℝ} (h : ContDiffAt ℝ ω f 0) (k : ContDiffAt ℝ ω g 0) :
    scalar (f*g) = scalar f * scalar g := by
  unfold scalar
  rw [←map_mul,←jet_mul (liftGreen h) (liftGreen k)]; rfl

theorem sub {f g : ℝ → ℝ} (h : ContDiffAt ℝ ω f 0) (k : ContDiffAt ℝ ω g 0) :
    scalar (f-g) = scalar f - scalar g := by
  unfold scalar
  rw [←map_sub,←jet_sub (liftGreen h) (liftGreen k)]; rfl

@[simp] theorem square : scalar (fun t : ℝ => t^2) = X^2 := by
  rw [show (fun t : ℝ => t^2) = (id : ℝ → ℝ)*id by funext t; simp [pow_two]]
  rw [mul contDiffAt_id contDiffAt_id,«variable»,pow_two]

theorem cleared {f : ℝ → ℝ} {P Q : PowerSeries ℝ} (h : ContDiffAt ℝ ω f 0)
    (balance : scalar f + X^2 * P = X^2 * Q) (i : ℕ) (quiet : coeff i Q = 0) :
    coeff i P = -((i+2).factorial:ℝ)⁻¹*iteratedDeriv (i+2) f 0 := by
  have obs := congrArg (coeff (i+2)) balance
  simp only [map_add,coeff_X_pow_mul',Nat.le_add_left,if_true,Nat.add_sub_cancel_right,quiet,numeric _ h] at obs
  linarith

end YM.Integration.OriginalRadialSeries
end
