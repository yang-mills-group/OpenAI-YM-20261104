import YM.Integration.LocalComparisonRetainedInput
import YM.Integration.LocalComparisonPreResetDensity

/-!
# Complete density bounds for retained marked inputs

These are conditional consequences of the existing full RelativeBudget on
one unchanged carrier. Regular, unit, caption and forced channels all remain.
The original vacuum KBound and combined smallness are explicit; no analytic
Prepared factorization, spatial output transport or new qlocal conclusion is
inferred. The normalized estimate divides by this same positive vacuum and
keeps the complete flagged exponential term.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.Global

open Lattice Wilson RG Marker RG3.Script.Picnic
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}
    {D : V → ComparisonDensity.Address.Orbit}
    {N period level : ℕ} {Q : StepCarrier C N period level}
    {roots : V → Site (C.side level period)} {w cost : V → ℝ}
    {regularPrice forcedPrice vacuum : ℝ}

/-- Full density control on each independent unit-test tuple, without
zeroing any marked regular, unit or caption channel. -/
theorem RetainedMarkedInput.full_density_error_price
    (I : RetainedMarkedInput (D := D) N period level Q roots w
      (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v)
    (hReserve : Q.rep.activities.KBound (C.path.levels.budget level) vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) *
      (forcedDivisor C level * forcedPrice) ≤ 1)
    (x : IndependentTests D) (U : Config G (C.side level period)) :
    Poly.price (fun v => w v / cost v)
      ((I.value.leaf (testInclusion D x)).density U -
        (Q.rep.eval U : ℂ) • (1 : Poly R)) ≤
      |Q.rep.eval U| * (Real.exp (Fintype.card V * regularPrice) - 1) +
      (Real.exp (Q.rep.exponent U) * Real.exp (Fintype.card V * regularPrice)) *
        (if flags Q.rep.p.threshold U = ∅ then 0 else
          ((Fintype.card V : ℝ) * (forcedDivisor C level * forcedPrice)) *
            Real.exp (-SectorNext.Vacuum.flagRate (C.path.levels.budget level) *
              (flags Q.rep.p.threshold U).card)) := by
  exact PreResetDensity.full_density_error_price I.price hcost
    (congrArg BudgetPoint.threshold Q.point).symm hReserve hSmall x U

/-- The same complete defect after division by the original positive vacuum.
The entire forced-gas charge remains divided by that vacuum. -/
theorem RetainedMarkedInput.normalized_density_error_price
    (I : RetainedMarkedInput (D := D) N period level Q roots w
      (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v)
    (hReserve : Q.rep.activities.KBound (C.path.levels.budget level) vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) *
      (forcedDivisor C level * forcedPrice) ≤ 1)
    (x : IndependentTests D) (U : Config G (C.side level period))
    (hVacuum : 0 < Q.rep.eval U) :
    Poly.price (fun v => w v / cost v)
      ((Q.rep.eval U : ℂ)⁻¹ • (I.value.leaf (testInclusion D x)).density U -
        (1 : Poly R)) ≤
      (Real.exp (Fintype.card V * regularPrice) - 1) +
      ((Real.exp (Q.rep.exponent U) * Real.exp (Fintype.card V * regularPrice)) *
        (if flags Q.rep.p.threshold U = ∅ then 0 else
          ((Fintype.card V : ℝ) * (forcedDivisor C level * forcedPrice)) *
            Real.exp (-SectorNext.Vacuum.flagRate (C.path.levels.budget level) *
              (flags Q.rep.p.threshold U).card))) / Q.rep.eval U := by
  have hq : (Q.rep.eval U : ℂ) ≠ 0 := by exact_mod_cast hVacuum.ne'
  have hraw := I.full_density_error_price hcost hReserve hSmall x U
  rw [abs_of_pos hVacuum] at hraw
  have hrewrite :
      (Q.rep.eval U : ℂ)⁻¹ • (I.value.leaf (testInclusion D x)).density U -
          (1 : Poly R) =
        (Q.rep.eval U : ℂ)⁻¹ •
          ((I.value.leaf (testInclusion D x)).density U -
            (Q.rep.eval U : ℂ) • (1 : Poly R)) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hq, one_smul]
  rw [hrewrite, Poly.adapted, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hVacuum]
  apply (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hVacuum.le)).trans_eq
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hVacuum.ne', one_mul,
    div_eq_mul_inv]
  ring

end YM.Integration.LocalComparison.Global
