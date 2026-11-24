import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

noncomputable section
namespace PhysicalMatching.H7IndependentMaxwellPupilKinematics
open scoped BigOperators

def determinant (x y : Fin 4 → ℝ) (a b : Fin 4) : ℝ := x a*y b-x b*y a

def sixPlanes (x y : Fin 4 → ℝ) : ℝ :=
  (determinant x y 0 1)^2 + ((determinant x y 0 2)^2 +
  ((determinant x y 0 3)^2 + ((determinant x y 1 2)^2 +
  ((determinant x y 1 3)^2 + (determinant x y 2 3)^2))))

theorem sixGram (x y : Fin 4 → ℝ) : sixPlanes x y =
    (∑ i : Fin 4, (x i)^2) * (∑ i : Fin 4, (y i)^2) - (∑ i : Fin 4, x i*y i)^2 := by
  simp only [sixPlanes, determinant, Fin.sum_univ_four]
  ring

def reflection (u : Fin 4 → ℝ) (rho : ℝ) (a i : Fin 4) : ℝ :=
  (if i=a then 1 else 0) - 2*u i*u a/rho

theorem columnInner (u : Fin 4 → ℝ) (rho : ℝ) (hr : rho ≠ 0)
    (hn : (∑ i : Fin 4, (u i)^2) = rho) (a b : Fin 4) :
    (∑ i : Fin 4, reflection u rho a i * reflection u rho b i) =
      (if a=b then (1:ℝ) else 0) := by
  have expand (i : Fin 4) :
      reflection u rho a i * reflection u rho b i =
        (if i=a then (if i=b then (1:ℝ) else 0) else 0)
        - (if i=a then 2*u i*u b/rho else 0)
        - (if i=b then 2*u i*u a/rho else 0)
        + ((u i)^2) * (4*u a*u b/rho^2) := by
    by_cases hab : a = b
    · subst b
      by_cases hi : i = a <;> simp [reflection, hi] <;> ring
    · have hba : b ≠ a := Ne.symm hab
      by_cases ha : i = a <;> by_cases hb : i = b <;>
        simp_all [reflection] <;> ring
  simp only [expand,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,hn]
  simp
  field_simp [hr]
  ring

theorem fullTrace (u : Fin 4 → ℝ) (rho : ℝ) (hr : rho ≠ 0)
    (hn : (∑ i : Fin 4, (u i)^2) = rho) (a b : Fin 4) (hab : a ≠ b) :
    sixPlanes (reflection u rho a) (reflection u rho b) = 1 := by
  rw [sixGram]
  simp only [pow_two]
  rw [columnInner u rho hr hn a a,columnInner u rho hr hn b b,columnInner u rho hr hn a b]
  simp [hab]

def radius (rho x s : ℝ) : ℝ := rho+2*x*s+s^2
def component23 (K rho x T s : ℝ) : ℝ := 4*K*(x+s)^2*T/(radius rho x s)^6
def traceProfile (K rho x s : ℝ) : ℝ := K/(radius rho x s)^4
def component01 (K rho x T s : ℝ) : ℝ := traceProfile K rho x s-component23 K rho x T s
def e23Profile (K rho x T s : ℝ) : ℝ :=
  K*(radius rho x s-2*T)^2/(radius rho x s)^6

theorem radiusDerivative (rho x : ℝ) : HasDerivAt (radius rho x) (2*x) 0 := by
  convert ((hasDerivAt_const (0:ℝ) rho).add
    ((hasDerivAt_id (0:ℝ)).const_mul (2*x))).add ((hasDerivAt_id (0:ℝ)).pow 2) using 1
  · rfl
  · rfl
  · funext t; rfl
  · simp

theorem component23Derivative (K rho x T : ℝ) (hr : rho ≠ 0) :
    HasDerivAt (component23 K rho x T) (8*K*x*T*(rho-6*x^2)/rho^7) 0 := by
  have h0 : (radius rho x 0)^6 ≠ 0 := by simpa [radius] using pow_ne_zero 6 hr
  have dx := (hasDerivAt_const (0:ℝ) x).add (hasDerivAt_id (0:ℝ))
  rw [show 8*K*x*T*(rho-6*x^2)/rho^7 =
      (4*K*(2*x)*T*rho^6-4*K*x^2*T*(6*rho^5*(2*x)))/(rho^6)^2 by
    field_simp [hr]
    ring]
  convert (((dx.pow 2).const_mul (4*K)).mul_const T).div
    ((radiusDerivative rho x).pow 6) h0 using 1
  · rfl
  · rfl
  · funext t; rfl
  · simp [radius]

theorem traceDerivative (K rho x : ℝ) (hr : rho ≠ 0) :
    HasDerivAt (traceProfile K rho x) (-8*K*x/rho^5) 0 := by
  have h0 : (radius rho x 0)^4 ≠ 0 := by simpa [radius] using pow_ne_zero 4 hr
  rw [show -8*K*x/rho^5 = -(K*(4*rho^3*(2*x)))/(rho^4)^2 by
    field_simp [hr]
    ring]
  convert (hasDerivAt_const (0:ℝ) K).div ((radiusDerivative rho x).pow 4) h0 using 1
  · rfl
  · rfl
  · funext t; rfl
  · simp [radius]

theorem component01Derivative (K rho x T : ℝ) (hr : rho ≠ 0) :
    HasDerivAt (component01 K rho x T) (-8*K*x/rho^5-8*K*x*T*(rho-6*x^2)/rho^7) 0 :=
  (traceDerivative K rho x hr).sub (component23Derivative K rho x T hr)

theorem e23Derivative (K rho x T : ℝ) (hr : rho ≠ 0) :
    HasDerivAt (e23Profile K rho x T) (-8*K*x*(rho-2*T)*(rho-3*T)/rho^7) 0 := by
  have r := radiusDerivative rho x
  have h0 : (radius rho x 0)^6 ≠ 0 := by simpa [radius] using pow_ne_zero 6 hr
  rw [show -8*K*x*(rho-2*T)*(rho-3*T)/rho^7 =
      (K*(2*(rho-2*T)*(2*x))*rho^6-K*(rho-2*T)^2*(6*rho^5*(2*x)))/(rho^6)^2 by
    field_simp [hr]
    ring]
  convert (((r.sub_const (2*T)).pow 2).const_mul K).div (r.pow 6) h0 using 1
  · rfl
  · rfl
  · funext t; rfl
  · simp [radius]

end PhysicalMatching.H7IndependentMaxwellPupilKinematics
end
