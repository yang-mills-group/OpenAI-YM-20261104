import YM.Integration.LocalComparisonFullPreparation

/-!
The same full preparation at an explicit requested norm. The physical
carrier and regulator stay original; only the norm paying the unchanged
rows is a parameter. This permits exact shared-level requested norms to
join without claiming control at larger native derivative orders.

Native-stage preparation embeds by choosing its native budget. A change
to a different norm requires a genuine budget restriction or construction.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.Global

open Filter Lattice Wilson RG Marker
open RG3.Script.Picnic Comparison.RG02
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}

structure PreparedWithRemainderAt {D : V → ComparisonDensity.Address.Orbit}
    (N period level : ℕ) (q : BudgetPoint) (Q : StepCarrier C N period level)
    (roots : V → Site (C.side level period))
    (input : Taste (TestSpace D) roots Q.rep R)
    (colors : TestSpace D → Bulk.Colors R G (C.side level period))
    (packets : MarkedPackets D G (C.side level period) R)
    (w : V → ℝ) (kernelEnvelope : R.Mode → ℝ)
    (regularPrice forcedPrice : ℝ) where
  convention : InputColors colors packets
  remainder : Taste (TestSpace D) roots Q.rep R
  full (x : TestSpace D) (U : Config G (C.side level period)) :
    (input.leaf x).density U =
      Poly.pass (packets.read x (Pert.Asymptotics.regulatorRun C N period level) U) *
        (remainder.leaf x).density U
  remainder_price : RelativeBudget q
    (pullback (testInclusion D) remainder) w (forcedDivisor C level)
    kernelEnvelope regularPrice forcedPrice

variable {D : V → ComparisonDensity.Address.Orbit}
    {N period level : ℕ} {q : BudgetPoint} {Q : StepCarrier C N period level}
    {roots : V → Site (C.side level period)}
    {input : Taste (TestSpace D) roots Q.rep R}
    {colors : TestSpace D → Bulk.Colors R G (C.side level period)}
    {packets : MarkedPackets D G (C.side level period) R}
    {w cost : V → ℝ} {regularPrice forcedPrice : ℝ}

/-- Choosing the original norm changes no datum or estimate. -/
def PreparedWithRemainder.atNative
    (h : PreparedWithRemainder N period level Q roots input colors packets w
      (envelopeProduct cost) regularPrice forcedPrice) :
    PreparedWithRemainderAt N period level (C.path.levels.budget level)
      Q roots input colors packets w (envelopeProduct cost) regularPrice forcedPrice where
  convention := h.convention
  remainder := h.remainder
  full := h.full
  remainder_price := h.remainder_price

/-- The exact native-norm specialization recovers the preserved interface. -/
def PreparedWithRemainderAt.toNative
    (h : PreparedWithRemainderAt N period level (C.path.levels.budget level)
      Q roots input colors packets w (envelopeProduct cost) regularPrice forcedPrice) :
    PreparedWithRemainder N period level Q roots input colors packets w
      (envelopeProduct cost) regularPrice forcedPrice where
  convention := h.convention
  remainder := h.remainder
  full := h.full
  remainder_price := h.remainder_price

omit [DecidableEq V] in
/-- The complete same-vacuum bound; the ordinary price has no forced divisor. -/
def retainedErrorBoundAt (q : BudgetPoint) (Q : StepCarrier C N period level)
    (regularPrice forcedPrice : ℝ) (U : Config G (C.side level period)) : ℝ :=
  (Real.exp (Fintype.card V * regularPrice) - 1) +
    ((Real.exp (Q.rep.exponent U) * Real.exp (Fintype.card V * regularPrice)) *
      (if flags Q.rep.p.threshold U = ∅ then 0 else
        ((Fintype.card V : ℝ) * (forcedDivisor C level * forcedPrice)) *
          Real.exp (-SectorNext.Vacuum.flagRate q *
            (flags Q.rep.p.threshold U).card))) / Q.rep.eval U

/-- Exact full normalized model-times-remainder identity, before any estimate. -/
theorem PreparedWithRemainderAt.normalized_defect
    (h : PreparedWithRemainderAt N period level q Q roots input colors packets w
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
theorem PreparedWithRemainderAt.normalized_remainder_price
    (h : PreparedWithRemainderAt N period level q Q roots input colors packets w
      (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v)
    (hthreshold : q.threshold = Q.rep.p.threshold) {vacuum : ℝ}
    (hReserve : Q.rep.activities.KBound q vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) *
      (forcedDivisor C level * forcedPrice) ≤ 1)
    (x : IndependentTests D) (U : Config G (C.side level period))
    (hVacuum : 0 < Q.rep.eval U) :
    Poly.price (fun v => w v / cost v)
      ((Q.rep.eval U : ℂ)⁻¹ •
        (h.remainder.leaf (testInclusion D x)).density U - 1) ≤
      retainedErrorBoundAt (V := V) q Q regularPrice forcedPrice U := by
  have hq : (Q.rep.eval U : ℂ) ≠ 0 := by exact_mod_cast hVacuum.ne'
  have hraw := PreResetDensity.full_density_error_price h.remainder_price hcost
    hthreshold hReserve hSmall x U
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
  unfold retainedErrorBoundAt
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hVacuum.ne', one_mul,
    div_eq_mul_inv]
  ring

/-- Multiplication retains every analytic/rough mixed term and the full
model factor. No full output is substituted for the model alone. -/
theorem PreparedWithRemainderAt.normalized_defect_price
    (h : PreparedWithRemainderAt N period level q Q roots input colors packets w
      (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v)
    (hthreshold : q.threshold = Q.rep.p.threshold) {vacuum : ℝ}
    (hReserve : Q.rep.activities.KBound q vacuum)
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
        retainedErrorBoundAt (V := V) q Q regularPrice forcedPrice U := by
  have hw : ∀ v, 0 < w v / cost v :=
    fun v => div_pos (h.remainder_price.budget.radii v) (hcost v)
  rw [h.normalized_defect]
  apply (Poly.multiplication hw _ _).trans
  exact mul_le_mul_of_nonneg_left
    (h.normalized_remainder_price hcost hthreshold hReserve hSmall x U hVacuum)
    (Poly.nonnegative hw _)

end YM.Integration.LocalComparison.Global
end
