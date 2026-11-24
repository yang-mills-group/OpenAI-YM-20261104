import YM.Integration.LocalComparisonRetainedDensity
import YM.Integration.LocalComparisonForcedFunding

/-!
Full-channel preparation retains its ordinary regular/unit/caption price a
separately from the divided forced price b. The normalized defect below is
the full model times its full remainder error. Its bound keeps exp(card*a)-1,
the original flagged factor, and the reciprocal of the same vacuum.

These are consequences of an already constructed preparation. They do not
turn a rough input into an analytic packet or assert the sharp analytic
qelt estimate for that rough input.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.Global

open Filter Lattice Wilson RG Marker
open RG3.Script.Picnic Comparison.RG02
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}
    {D : V → ComparisonDensity.Address.Orbit}
    {N period level : ℕ} {Q : StepCarrier C N period level}
    {roots : V → Site (C.side level period)}
    {input : Taste (TestSpace D) roots Q.rep R}
    {colors : TestSpace D → Bulk.Colors R G (C.side level period)}
    {packets : MarkedPackets D G (C.side level period) R}
    {w cost : V → ℝ} {regularPrice forcedPrice : ℝ}

omit [DecidableEq V] in
/-- The complete same-vacuum bound; the ordinary price has no forced divisor. -/
def retainedErrorBound (Q : StepCarrier C N period level)
    (regularPrice forcedPrice : ℝ) (U : Config G (C.side level period)) : ℝ :=
  (Real.exp (Fintype.card V * regularPrice) - 1) +
    ((Real.exp (Q.rep.exponent U) * Real.exp (Fintype.card V * regularPrice)) *
      (if flags Q.rep.p.threshold U = ∅ then 0 else
        ((Fintype.card V : ℝ) * (forcedDivisor C level * forcedPrice)) *
          Real.exp (-SectorNext.Vacuum.flagRate (C.path.levels.budget level) *
            (flags Q.rep.p.threshold U).card))) / Q.rep.eval U

/-- Exact full normalized model-times-remainder identity, before any estimate. -/
theorem PreparedWithRemainder.normalized_defect
    (h : PreparedWithRemainder N period level Q roots input colors packets w
      (envelopeProduct cost) regularPrice forcedPrice)
    (x : TestSpace D) (U : Config G (C.side level period)) :
    (Q.rep.eval U : ℂ)⁻¹ • (input.leaf x).density U -
        Poly.pass (packets.read x
          (Pert.Asymptotics.regulatorRun C N period level) U) =
      Poly.pass (packets.read x
          (Pert.Asymptotics.regulatorRun C N period level) U) *
        ((Q.rep.eval U : ℂ)⁻¹ • (h.remainder.leaf x).density U - 1) := by
  rw [h.full, mul_sub, mul_one, mul_smul_comm]

/-- The complete remainder estimate needs only its actual common budget,
the same carrier's K bound and the native combined forced smallness. -/
theorem PreparedWithRemainder.normalized_remainder_price
    (h : PreparedWithRemainder N period level Q roots input colors packets w
      (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) {vacuum : ℝ}
    (hReserve : Q.rep.activities.KBound (C.path.levels.budget level) vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) *
      (forcedDivisor C level * forcedPrice) ≤ 1)
    (x : IndependentTests D) (U : Config G (C.side level period))
    (hVacuum : 0 < Q.rep.eval U) :
    Poly.price (fun v => w v / cost v)
      ((Q.rep.eval U : ℂ)⁻¹ •
        (h.remainder.leaf (testInclusion D x)).density U - 1) ≤
      retainedErrorBound (V := V) Q regularPrice forcedPrice U := by
  have hq : (Q.rep.eval U : ℂ) ≠ 0 := by exact_mod_cast hVacuum.ne'
  have hraw := PreResetDensity.full_density_error_price h.remainder_price hcost
    (congrArg BudgetPoint.threshold Q.point).symm hReserve hSmall x U
  rw [abs_of_pos hVacuum] at hraw
  have hrewrite :
      (Q.rep.eval U : ℂ)⁻¹ •
          (h.remainder.leaf (testInclusion D x)).density U - (1 : Poly R) =
        (Q.rep.eval U : ℂ)⁻¹ •
          ((h.remainder.leaf (testInclusion D x)).density U -
            (Q.rep.eval U : ℂ) • (1 : Poly R)) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hq, one_smul]
  rw [hrewrite, Poly.adapted, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hVacuum]
  apply (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hVacuum.le)).trans_eq
  unfold retainedErrorBound
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hVacuum.ne', one_mul,
    div_eq_mul_inv]
  ring

/-- Multiplication retains every analytic/rough mixed term and the full
model factor. No full output is substituted for the model alone. -/
theorem PreparedWithRemainder.normalized_defect_price
    (h : PreparedWithRemainder N period level Q roots input colors packets w
      (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) {vacuum : ℝ}
    (hReserve : Q.rep.activities.KBound (C.path.levels.budget level) vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) *
      (forcedDivisor C level * forcedPrice) ≤ 1)
    (x : IndependentTests D) (U : Config G (C.side level period))
    (hVacuum : 0 < Q.rep.eval U) :
    Poly.price (fun v => w v / cost v)
      ((Q.rep.eval U : ℂ)⁻¹ • (input.leaf (testInclusion D x)).density U -
        Poly.pass (packets.read (testInclusion D x)
          (Pert.Asymptotics.regulatorRun C N period level) U)) ≤
      Poly.price (fun v => w v / cost v)
        (Poly.pass (packets.read (testInclusion D x)
          (Pert.Asymptotics.regulatorRun C N period level) U)) *
        retainedErrorBound (V := V) Q regularPrice forcedPrice U := by
  have hw : ∀ v, 0 < w v / cost v :=
    fun v => div_pos (h.remainder_price.budget.radii v) (hcost v)
  rw [h.normalized_defect]
  apply (Poly.multiplication hw _ _).trans
  exact mul_le_mul_of_nonneg_left
    (h.normalized_remainder_price hcost hReserve hSmall x U hVacuum)
    (Poly.nonnegative hw _)

omit [DecidableEq V] in
/-- A fixed upper bound on the divided forced input price is paid on the
original schedule. This makes no smallness claim about ordinary regular a. -/
theorem eventually_retained_forced_smallness (C : Family G) (hG : G.Simple)
    (bound : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ b : ℝ, b ≤ bound →
      C.path.levels.clock.forcedAllowance (m + 1) + (Fintype.card V : ℝ) *
        (forcedDivisor C (m + 1) * b) ≤ 1 := by
  have hRoot := forcedDivisor_tendsto C hG
  have hTotal : Tendsto (fun m : ℕ =>
      (forcedDivisor C m)^2 +
        (Fintype.card V : ℝ) * (forcedDivisor C m * bound))
      atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, zero_add] using
      (hRoot.pow 2).add ((hRoot.mul_const bound).const_mul (Fintype.card V : ℝ))
  obtain ⟨start, hStart⟩ := eventually_atTop.mp
    (hTotal.eventually (gt_mem_nhds zero_lt_one))
  filter_upwards [eventually_ge_atTop start] with m hm b hb
  have hDivisor : 0 ≤ forcedDivisor C (m + 1) := Real.sqrt_nonneg _
  have hSquare : (forcedDivisor C (m + 1))^2 =
      C.path.levels.clock.forcedAllowance (m + 1) :=
    Real.sq_sqrt (Real.exp_pos _).le
  calc
    _ ≤ C.path.levels.clock.forcedAllowance (m + 1) +
        (Fintype.card V : ℝ) * (forcedDivisor C (m + 1) * bound) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb hDivisor) (Nat.cast_nonneg _))
    _ = (forcedDivisor C (m + 1))^2 +
        (Fintype.card V : ℝ) * (forcedDivisor C (m + 1) * bound) := by rw [hSquare]
    _ ≤ 1 := (hStart (m + 1) (by omega)).le

end YM.Integration.LocalComparison.Global
end
