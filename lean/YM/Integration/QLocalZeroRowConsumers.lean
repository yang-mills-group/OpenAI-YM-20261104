import YM.AnalyticBridge.VERIFIED_RESET_STEP.Calculus

/-!
Function-level consequences for dormant original vacuum rows.
The atom, row label, root and support are never replaced. These lemmas do
not assert that a zero atom's stored footprint lies in its row support,
and do not change Global.VacuumPackets or any qlocal target.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.ZeroRows

open Lattice Wilson RG
open AnalyticBridge.VerifiedReset
open scoped BigOperators

variable {G : Gauge} {n : Side} {k : ℕ}
variable (a : Atom G k)

/-- Vanishing coefficient mass makes the unchanged atom read zero everywhere. -/
theorem unmasked_zero (hzero : a.magnitude = 0) (o : Site n)
    (U : Config G n) : a.unmasked U o = 0 := by
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  simpa only [hzero, zero_mul] using a.unmasked_bound U o

private theorem function_zero (hzero : a.magnitude = 0) (o : Site n) :
    (fun U : Config G n => a.unmasked U o) = fun _ => 0 :=
  funext fun U => unmasked_zero a hzero o U

/-- Every original row support carries the zero function with exactly zero
derivative price, independently of the atom's syntactic footprint. -/
theorem regular_bounds_zero (hzero : a.magnitude = 0)
    (p : BudgetPoint) (o : Site n) (S : Support n) :
    p.Regular S (fun U => a.unmasked U o) ∧
      p.supBounds o S (fun U => a.unmasked U o) 0 := by
  rw [function_zero a hzero o]
  exact ⟨reg_const 0, by simpa only [abs_zero] using
    (sup_const (p := p) (o := o) (X := S) (0 : ℝ))⟩

/-- Every choice of the original mask support keeps a dormant read zero. -/
theorem masked_zero (hzero : a.magnitude = 0)
    (t : ℝ) (o : Site n) (S : Support n) :
    masked t S (fun U => a.unmasked U o) = 0 := by
  rw [function_zero a hzero o]
  funext U
  simp only [masked, Set.indicator_zero, Pi.zero_apply]

/-- Original exponential path and cover charges of a zero row vanish. -/
theorem mass_zero (hzero : a.magnitude = 0)
    (p : BudgetPoint) (S : Support n) (width : ℝ) :
    p.mass S (a.budget width) = 0 := by
  simp only [BudgetPoint.mass, Atom.budget, hzero, zero_mul, mul_zero]

/-- The same regularity and derivative price extend to the original row
support using geometric containment only for a nonzero coefficient row. -/
theorem regular_bounds_of_nonzero_support
    (p : BudgetPoint) (o : Site n) (S : Support n) (c : ℝ)
    (hregular : p.Regular (a.footprint o) (fun U => a.unmasked U o))
    (hbound : p.supBounds o (a.footprint o) (fun U => a.unmasked U o) c)
    (hsupport : a.magnitude ≠ 0 → a.footprint o ⊆ S) :
    p.Regular S (fun U => a.unmasked U o) ∧
      p.supBounds o S (fun U => a.unmasked U o) c := by
  by_cases hzero : a.magnitude = 0
  · obtain ⟨hr, hb⟩ := regular_bounds_zero a hzero p o S
    exact ⟨hr, sup_le hb hbound.1⟩
  · exact ⟨reg_larger hregular (hsupport hzero),
      sup_larger hbound (hsupport hzero)⟩

/-- The original weighted cover bill needs its geometric inequality only
on nonzero coefficient rows. No unweighted cover inequality is concluded. -/
theorem mass_budget_of_nonzero_cover
    (p : BudgetPoint) (S : Support n) (width offset : ℝ)
    (hcover : a.magnitude ≠ 0 →
      p.supportExponent * (coverNumber p.B S : ℝ) ≤
        p.supportExponent * offset + width * a.length) :
    p.mass S a.magnitude ≤
      Real.exp (p.supportExponent * offset) * a.budget width := by
  by_cases hzero : a.magnitude = 0
  · simp only [BudgetPoint.mass, Atom.budget, hzero, mul_zero, zero_mul, le_refl]
  · have hm : 0 ≤ a.magnitude := by
      unfold Atom.magnitude
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc
      p.mass S a.magnitude =
          Real.exp (p.supportExponent * (coverNumber p.B S : ℝ)) * a.magnitude := rfl
      _ ≤ Real.exp (p.supportExponent * offset + width * a.length) * a.magnitude :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hcover hzero)) hm
      _ = Real.exp (p.supportExponent * offset) * a.budget width := by
        rw [Real.exp_add]
        unfold Atom.budget
        ring

end YM.Integration.FullQLocal.ZeroRows
end
