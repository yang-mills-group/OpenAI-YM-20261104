import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import YM.RG06.TaylorGerm

/-!
# Univariate coefficients for the Wilson stencil calculus

Ordinary (factorial-*divided*) Taylor coefficients over ℝ.
The product law is also used with matrix coefficients (order matters).
No assumptions about analyticity in the running coupling of any actual correlation.
-/

set_option autoImplicit false
noncomputable section

namespace YM.RG06
open scoped ContDiff BigOperators

section Vector
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ordinary Taylor coefficients about *zero*, totalized by Lean where derivatives do not
exist. Used with separately proved smoothness. -/
def tcoef (f : ℝ → E) (k : ℕ) : E := (k.factorial : ℝ)⁻¹ • iteratedDeriv k f 0

@[simp] theorem tcoef_zero (f : ℝ → E) : tcoef f 0 = f 0 := by simp [tcoef]

theorem tcoef_const (e : E) (k : ℕ) :
    tcoef (fun _ => e) k = if k = 0 then e else 0 := by
  cases k <;> simp [tcoef, iteratedDeriv_const]

theorem tcoef_clm {f : ℝ → E} (L : E →L[ℝ] F) (k : ℕ) (h : ContDiffAt ℝ k f 0) :
    tcoef (fun t => L (f t)) k = L (tcoef f k) := by
  rw [mapEq]
where
  mapEq : tcoef (fun t => L (f t)) k = L (tcoef f k) := by
    unfold tcoef
    rw [map_smul]
    congr 1
    change iteratedDeriv k (L ∘ f) _ = _
    simp only [iteratedDeriv_eq_iteratedFDeriv,
      ContinuousLinearMap.iteratedFDeriv_comp_left L h le_rfl]
    rfl

@[simp] theorem tcoef_smul (f : ℝ → E) (c : ℝ) (k : ℕ) :
    tcoef (fun t => c • f t) k = c • tcoef f k := by
  unfold tcoef
  rw [iteratedDeriv_fun_const_smul_field, smul_comm]

theorem tcoef_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → E) (k : ℕ)
    (h : ∀ i ∈ s, ContDiffAt ℝ k (f i) 0) :
    tcoef (fun t => ∑ i ∈ s, f i t) k = ∑ i ∈ s, tcoef (f i) k := by
  simp only [tcoef, iteratedDeriv_fun_sum h, Finset.smul_sum]

theorem tcoef_neg (f : ℝ → E) (k : ℕ) :
    tcoef (fun t => - f t) k = - tcoef f k := by simp only [tcoef, iteratedDeriv_fun_neg, smul_neg]

end Vector

section Ring
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] {f g : ℝ → E}

theorem tcoef_mul (k : ℕ) (hf : ContDiffAt ℝ k f 0) (hg : ContDiffAt ℝ k g 0) :
    tcoef (f*g) k = ∑ i ∈ Finset.range (k+1), tcoef f i * tcoef g (k-i) := by
  rw [tcoef, iteratedDeriv_mul hf hg, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have h : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have he : (k.choose i : ℝ) * i.factorial * (k-i).factorial = k.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  simp only [tcoef, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  congr 1
  field_simp
  linarith

/-- Real Taylor series viewed as a formal algebraic object. -/
def rayTaylor (f : ℝ → E) : PowerSeries E := PowerSeries.mk (tcoef f)

@[simp] theorem coeff_rayTaylor (k : ℕ) : PowerSeries.coeff k (rayTaylor f) = tcoef f k := by
  rw [rayTaylor, PowerSeries.coeff_mk]

theorem rayTaylor_mul (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    rayTaylor (fun t => f t * g t) = rayTaylor f * rayTaylor g := by
  apply PowerSeries.ext
  intro k
  rw [coeff_rayTaylor, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_rayTaylor]
  have he : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  exact tcoef_mul k (hf.of_le he) (hg.of_le he)

theorem rayTaylor_add (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    rayTaylor (fun t => f t + g t) = rayTaylor f + rayTaylor g := by
  apply PowerSeries.ext
  intro k
  have he : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  simp only [map_add, coeff_rayTaylor, tcoef,
    iteratedDeriv_fun_add (hf.of_le he) (hg.of_le he), smul_add]

@[simp] theorem rayTaylor_const (e : E) : rayTaylor (fun _ => e) = PowerSeries.C e := by
  ext k; rw [coeff_rayTaylor, tcoef_const, PowerSeries.coeff_C]

end Ring

section Eval
variable {ι : Type*} (P : MvPolynomial ι ℂ) (f : ℝ → ι → ℂ)

theorem smooth_aeval {u : WithTop ℕ∞} (h : ∀ i, ContDiffAt ℝ u (fun t => f t i) 0) :
    ContDiffAt ℝ u (fun t => MvPolynomial.aeval (f t) P) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.aeval_C]; exact contDiffAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (h i)

theorem rayTaylor_aeval (h : ∀ i, ContDiffAt ℝ ∞ (fun t => f t i) 0) :
    rayTaylor (fun t => MvPolynomial.aeval (f t) P) =
      MvPolynomial.eval₂Hom PowerSeries.C (fun i => rayTaylor fun t => f t i) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add]; rw [rayTaylor_add (smooth_aeval p f h) (smooth_aeval q f h), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X']
    rw [rayTaylor_mul (smooth_aeval p f h) (h i), hp]

end Eval
end YM.RG06
