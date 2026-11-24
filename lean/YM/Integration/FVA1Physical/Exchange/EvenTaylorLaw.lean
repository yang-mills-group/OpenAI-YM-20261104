import YM.Integration.FVA1Physical.Exchange.FiniteWeightIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! An even partial sum of the ordinary exponential series is everywhere
positive. It determines an honest finite-order density on hot fields as well
as on the purchased curvature sector. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.FVA1Physical.FibreMeasure
open Set MeasureTheory
open scoped BigOperators

private theorem polynomial_step (n : ℕ) (x : ℝ) :
    weightJet (n+1) x = weightJet n x + tiltCoeff n * x^(n+1) := by
  simp only [weightJet,Finset.sum_range_succ,add_assoc]

private theorem polynomial_derivative (n : ℕ) (x : ℝ) :
    HasDerivAt (weightJet n) (weightJet n x - (n.factorial:ℝ)⁻¹*x^n) x := by
  induction n with
  | zero =>
    have z : weightJet 0=(fun _ => (1:ℝ)) := funext (fun t => by simp [weightJet])
    rw [z];simpa using hasDerivAt_const x (1:ℝ)
  | succ n ih =>
    have term := (hasDerivAt_pow (n+1) x).const_mul (tiltCoeff n)
    have coefficient : tiltCoeff n*((n+1:ℕ):ℝ)=(n.factorial:ℝ)⁻¹ := by
      rw [tiltCoeff,Nat.factorial_succ,Nat.cast_mul]
      have pos : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
      rw [mul_inv_rev,mul_assoc,inv_mul_cancel₀ pos.ne',mul_one]
    have sum := ih.add term
    have same : weightJet (n+1) = weightJet n + fun y => tiltCoeff n*y^(n+1) :=
      funext (fun t => polynomial_step n t)
    have value : weightJet (n+1) x-((n+1).factorial:ℝ)⁻¹*x^(n+1) =
       weightJet n x-(n.factorial:ℝ)⁻¹*x^n+tiltCoeff n*(((n+1:ℕ):ℝ)*x^(n+1-1)) := by
      rw [polynomial_step,Nat.succ_sub_one,←mul_assoc,coefficient]
      change weightJet n x+tiltCoeff n*x^(n+1)-tiltCoeff n*x^(n+1)=_
      ring
    rw [value,same];exact sum

theorem even_weight_positive (n : ℕ) (x : ℝ) : 0 < weightJet (2*n) x := by
  by_cases xp : 0≤x
  · unfold weightJet
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun j _ => by
      unfold tiltCoeff;positivity))
  let F := fun t : ℝ => weightJet (2*n) t * Real.exp (-t)
  have derivF (t : ℝ) : HasDerivAt F
      (-(((2*n).factorial:ℝ)⁻¹ * t^(2*n)) * Real.exp (-t)) t := by
    have exp := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    have product := (polynomial_derivative (2*n) t).mul exp
    have scalar : -(((2*n).factorial:ℝ)⁻¹*t^(2*n))*Real.exp (-t) =
        (weightJet (2*n) t-((2*n).factorial:ℝ)⁻¹*t^(2*n))*Real.exp (-t)+
          weightJet (2*n) t*(Real.exp (-t)*(-1)) := by ring
    rw [scalar];exact product
  have falling : Antitone F := antitone_of_deriv_nonpos (fun t => (derivF t).differentiableAt)
    (fun t => by rw [(derivF t).deriv];apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_nonneg _)
                 apply neg_nonpos.mpr;exact mul_nonneg (by positivity) ((even_two_mul n).pow_nonneg t))
  have nonzero : 0 < F x := lt_of_lt_of_le (a:=0) (b:=F 0) (by simp [F,weightJet]) (falling (le_of_not_ge xp))
  exact pos_of_mul_pos_left nonzero (Real.exp_pos _).le

end YM.Integration.FVA1Physical.FibreMeasure
