import YM.Push.LOOP_COEFFICIENT.Paths.Calculus
import YM.Comparison.RG02.Assembly.Vertices
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Data.Nat.Choose.Basic

/-!
# Exact mixed slots of a separated analytic product

The slot tuple has precisely the supplied field slots and the pure coupling
slots, in the native block order followed by an arbitrary explicit permutation.
The normalized identity keeps the factorial ratio; no dimension or norm of a
coordinate expansion enters the estimate.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeMixedSlotProduct

open Function
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complete separated function on the original product space. -/
def product (h : ℝ → ℝ) (f : E → ℝ) (z : ℝ × E) : ℝ :=
  h z.1 * f z.2

/-- Native block order: the field slots followed by the coupling slots. -/
def slots (c : ℕ) {d : ℕ} (v : Fin d → E) : Fin (c + d) → ℝ × E :=
  Push.Loops.Paths.prepend (fun _ : Fin c => (1, 0)) (fun i => (0, v i))

private lemma block_derivative {h : ℝ → ℝ} {f : E → ℝ}
    (hh : ContDiffAt ℝ ω h 0) (hf : ContDiffAt ℝ ω f 0)
    (c d : ℕ) (v : Fin d → E) :
    iteratedFDeriv ℝ (c + d) (product h f) 0 (slots c v) =
      iteratedFDeriv ℝ c h 0 (fun _ => 1) *
        iteratedFDeriv ℝ d f 0 v := by
  let A : (ℝ × E) →L[ℝ] (ℝ × E) :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod 0
  let B : (ℝ × E) →L[ℝ] (ℝ × E) :=
    (0 : (ℝ × E) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ E)
  let u : Fin c → ℝ × E := fun _ => (1, 0)
  let w : Fin d → ℝ × E := fun i => (0, v i)
  let H := iteratedFDeriv ℝ c h 0 (fun _ => 1)
  have hp : ContDiffAt ℝ ω (fun a : ℝ × E => h a.1) 0 :=
    hh.comp 0 contDiffAt_fst
  have hq : ContDiffAt ℝ ω (fun b : ℝ × E => f b.2) 0 :=
    hf.comp 0 contDiffAt_snd
  have hprod : ContDiffAt ℝ ω (product h f) 0 := hp.mul hq
  have hfst : iteratedFDeriv ℝ c (fun a : ℝ × E => h a.1) 0 u = H := by
    simpa [u, H] using
      (Push.Loops.Paths.iterated_affine (f := h) (r := c)
        (ContinuousLinearMap.fst ℝ ℝ E) 0 0 (by simpa using hh) u)
  have hsnd : iteratedFDeriv ℝ d (fun b : ℝ × E => f b.2) 0 w =
      iteratedFDeriv ℝ d f 0 v := by
    simpa [w] using
      (Push.Loops.Paths.iterated_affine (f := f) (r := d)
        (ContinuousLinearMap.snd ℝ ℝ E) 0 0 (by simpa using hf) w)
  have inner (b : ℝ × E) :
      iteratedFDeriv ℝ c (fun a => product h f (B b + A a)) 0 u =
        H * f b.2 := by
    have hab : (fun a => product h f (B b + A a)) =
        (fun a : ℝ × E => h a.1 * f b.2) := by
      funext a
      simp [product, A, B]
    rw [hab]
    have he := congrArg (fun T => T u)
      (iteratedFDeriv_smul_const_apply (v := f b.2) (hp.of_le le_top))
    change iteratedFDeriv ℝ c (fun a : ℝ × E => h a.1 * f b.2) 0 u =
      iteratedFDeriv ℝ c (fun a : ℝ × E => h a.1) 0 u * f b.2 at he
    rw [hfst] at he
    exact he
  have outer : iteratedFDeriv ℝ d (fun b : ℝ × E => H * f b.2) 0 w =
      H * iteratedFDeriv ℝ d f 0 v := by
    have he := congrArg (fun T => T w)
      (iteratedFDeriv_const_smul_apply' (a := H) (hq.of_le le_top))
    change iteratedFDeriv ℝ d (fun b : ℝ × E => H * f b.2) 0 w =
      H * iteratedFDeriv ℝ d (fun b : ℝ × E => f b.2) 0 w at he
    rw [hsnd] at he
    exact he
  have hsplit := Push.Loops.Paths.mixed_partial A B hprod u w
  rw [show (fun b => iteratedFDeriv ℝ c
      (fun a => product h f (B b + A a)) 0 u) =
      (fun b : ℝ × E => H * f b.2) from funext inner] at hsplit
  change iteratedFDeriv ℝ d (fun b : ℝ × E => H * f b.2) 0 w =
    iteratedFDeriv ℝ (c + d) (product h f) 0 (slots c v) at hsplit
  exact hsplit.symm.trans outer

/-- The raw derivative has one surviving assignment of the pure slot types. -/
theorem mixed_derivative {h : ℝ → ℝ} {f : E → ℝ}
    (hh : AnalyticAt ℝ h 0) (hf : AnalyticAt ℝ f 0)
    (c d : ℕ) (v : Fin d → E) (σ : Equiv.Perm (Fin (c + d))) :
    iteratedFDeriv ℝ (c + d) (product h f) 0 (slots c v ∘ σ) =
      iteratedFDeriv ℝ c h 0 (fun _ => 1) *
        iteratedFDeriv ℝ d f 0 v := by
  have hc : ContDiffAt ℝ ω h 0 := hh.contDiffAt
  have hd : ContDiffAt ℝ ω f 0 := hf.contDiffAt
  have hp : ContDiffAt ℝ ω (product h f) 0 :=
    (hc.comp 0 contDiffAt_fst).mul (hd.comp 0 contDiffAt_snd)
  rw [hp.iteratedFDeriv_comp_perm]
  exact block_derivative hc hd c d v

/-- Exact factorial-normalized mixed coefficient, including either zero order. -/
theorem normalized_mixed {h : ℝ → ℝ} {f : E → ℝ}
    (hh : AnalyticAt ℝ h 0) (hf : AnalyticAt ℝ f 0)
    (c d : ℕ) (v : Fin d → E) (σ : Equiv.Perm (Fin (c + d))) :
    (((c + d).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (c + d) (product h f) 0 (slots c v ∘ σ) =
      ((c.factorial : ℝ) * (d.factorial : ℝ) / ((c + d).factorial : ℝ)) *
        Comparison.RG02.Assembly.jet h c 1 *
        ((d.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ d f 0 v) := by
  rw [mixed_derivative hh hf]
  simp only [Comparison.RG02.Assembly.jet, smul_eq_mul, div_eq_mul_inv]
  have hc : (c.factorial : ℝ) ≠ 0 := by positivity
  have hd : (d.factorial : ℝ) ≠ 0 := by positivity
  symm
  calc
    _ = ((c.factorial : ℝ) * (c.factorial : ℝ)⁻¹) *
        ((d.factorial : ℝ) * (d.factorial : ℝ)⁻¹) *
        (((c + d).factorial : ℝ)⁻¹ *
          (iteratedFDeriv ℝ c h 0 (fun _ => 1) * iteratedFDeriv ℝ d f 0 v)) := by
      ring
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hd, one_mul, one_mul]

/-- Normalization pays the shuffle factorial without a dimension factor. -/
theorem normalized_bound {h : ℝ → ℝ} {f : E → ℝ}
    (hh : AnalyticAt ℝ h 0) (hf : AnalyticAt ℝ f 0)
    (c d : ℕ) (v : Fin d → E) (σ : Equiv.Perm (Fin (c + d))) :
    |(((c + d).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (c + d) (product h f) 0 (slots c v ∘ σ)| ≤
      |Comparison.RG02.Assembly.jet h c 1| *
        |(d.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ d f 0 v| := by
  let q : ℝ := (c.factorial : ℝ) * (d.factorial : ℝ) /
    ((c + d).factorial : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    apply (div_le_one (by positivity : 0 < ((c + d).factorial : ℝ))).2
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (c + d))
      (Nat.factorial_mul_factorial_dvd_factorial_add c d)
  rw [normalized_mixed hh hf, abs_mul, abs_mul, abs_of_nonneg hq]
  calc
    _ = q * (|Comparison.RG02.Assembly.jet h c 1| *
        |(d.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ d f 0 v|) := by ring
    _ ≤ 1 * (|Comparison.RG02.Assembly.jet h c 1| *
        |(d.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ d f 0 v|) :=
      mul_le_mul_of_nonneg_right hq1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := one_mul _

end YM.Integration.NativeMixedSlotProduct
end
