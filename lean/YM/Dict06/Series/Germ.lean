import YM.Gauge.Chart
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic
/-!
Unrestricted formal power-series convention, **ordinary coefficients**
(iterated derivative on a real line, DIVIDE by order factorial); the
letter/slot amplitude may be reexpressed but we never take a Taylor
coefficient of a physical measure. This module also applies when the
coefficient algebra is the representation matrix algebra; in products the
left coefficients always stand to the left.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Series
open PowerSeries Filter Function
open scoped Topology ContDiff BigOperators

section Additive
-- PowerSeries E (MvPowerSeries Unit E) is usable without a ring on E,
-- but coeff and mk currently require Semiring. keep a plain function
-- for translating Color jets.
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def ordinary (n : ℕ) (f : ℝ → E) : E := (n.factorial:ℝ)⁻¹ • iteratedDeriv n f 0

lemma ordinary_map (f : ℝ → E) (n : ℕ) (hf : ContDiffAt ℝ n f 0) (L : E →L[ℝ] F) :
    ordinary n (L ∘ f) = L (ordinary n f) := by
  simp only [ordinary,iteratedDeriv_eq_iteratedFDeriv, map_smul, L.iteratedFDeriv_comp_left hf le_rfl]
  rfl

@[simp] lemma ordinary_const (x : E) (n : ℕ) :
    ordinary n (fun _ => x) = if n=0 then x else 0 := by
  by_cases h : n=0
  · subst n; simp [ordinary, iteratedDeriv_zero]
  simp [ordinary, iteratedDeriv_const,h]

lemma ordinary_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → E) (n : ℕ)
    (h : ∀ i∈s, ContDiffAt ℝ n (f i) 0) :
    ordinary n (fun t=>∑ i∈s,f i t)=∑ i∈s,ordinary n (f i) := by
  simp only [ordinary, iteratedDeriv_fun_sum h, Finset.smul_sum]

lemma ordinary_add (n : ℕ) (f g : ℝ → E)
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0) :
    ordinary n (f+g) = ordinary n f + ordinary n g := by
  rw [ordinary,iteratedDeriv_add hf hg,smul_add]; rfl
lemma ordinary_eq_of_eventual (n : ℕ) {f g : ℝ→E}
    (he : f =ᶠ[𝓝 0] g) : ordinary n f=ordinary n g := by
  unfold ordinary; rw [Filter.EventuallyEq.iteratedDeriv_eq n he]

end Additive

section Ring

private lemma choose_div (n i : ℕ) (hi : i ≤ n) :
    (n.factorial:ℝ)⁻¹ * n.choose i = (i.factorial:ℝ)⁻¹ * ((n-i).factorial:ℝ)⁻¹ := by
  have he : (n.choose i : ℝ) * i.factorial * (n-i).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  field_simp
  linarith [he] -- maybe already simp

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
lemma ordinary_mul (n : ℕ) (f g : ℝ → R)
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0) :
    ordinary n (f*g) = ∑ i∈Finset.range (n+1), ordinary i f * ordinary (n-i) g := by
  simp only [ordinary, iteratedDeriv_mul hf hg, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro i hi
  let a := iteratedDeriv i f 0
  let b := iteratedDeriv (n - i) g 0
  change (n.factorial:ℝ)⁻¹ • ((n.choose i:R) * a * b) =
    ((i.factorial:ℝ)⁻¹ • a) * ((((n-i).factorial:ℝ)⁻¹) • b)
  rw [←nsmul_eq_mul,←Nat.cast_smul_eq_nsmul ℝ (n.choose i), Algebra.smul_mul_assoc,
      Algebra.smul_mul_assoc, mul_smul_comm,smul_smul,smul_smul, choose_div n i (by simpa using hi)]

def ps (f : ℝ→R) : PowerSeries R := PowerSeries.mk fun n => ordinary n f
@[simp] lemma ps_at (f : ℝ→R) (n : ℕ) : PowerSeries.coeff n (ps f) = ordinary n f := coeff_mk ..

lemma ps_one : ps (1:ℝ→R) = 1 := by ext1 n; change coeff n (ps (fun _=>1))=(coeff (R:=R) n) 1; simp
lemma ps_const (x : R) : ps (fun _=>x) = PowerSeries.C x := by ext1 n; simp [PowerSeries.coeff_C]
lemma ps_add (f g : ℝ→R) (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    ps (f+g)=ps f + ps g := by
  ext1 n; have hn : (n:WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  rw [map_add,ps_at,ps_at,ps_at,ordinary_add _ _ _ (hf.of_le hn) (hg.of_le hn)]
lemma ps_mul (f g : ℝ→R) (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    ps (f*g)=ps f * ps g := by
  ext1 n; have hn : (n:WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (ps f)*coeff j (ps g)) n]
  simp only [ps_at, ordinary_mul _ _ _ (hf.of_le hn) (hg.of_le hn)]

section complete
variable [CompleteSpace R]
open NormedSpace
lemma iterated_exp_mul (n : ℕ) (x : R) :
    iteratedDeriv n (fun t:ℝ=> exp (t • x)) = fun t=> exp (t • x) * x^n := by
  induction n with
  | zero => ext1 t; simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]; funext t
    rw [((hasDerivAt_exp_smul_const x t).mul_const (x^n)).deriv, mul_assoc,pow_succ']
lemma exponential (x : R) :
    ps (fun t:ℝ=> exp (t • x)) = PowerSeries.mk (fun n=> (n.factorial:ℝ)⁻¹ • x^n) := by
  ext1 n; rw [ps_at, ordinary, coeff_mk, iterated_exp_mul]; simp
end complete
end Ring

end YM.Dict06.Series
