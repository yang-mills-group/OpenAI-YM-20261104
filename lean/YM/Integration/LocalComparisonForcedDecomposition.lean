import YM.Integration.LocalComparisonPhysicalReadout
import YM.Integration.ActualNormalizedPush

/-!
Exact separation of the regular/caption error from the forced-gas error.
The latter is kept as an explicit unnormalized numerator, suitable for
integration under the actual law.  There is no pointwise inverse-vacuum
bound and no assumption that the forced numerator is already small.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker RG3.Forms RG3.Script.Picnic
open UniformPolynomialComparison
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
    {G : Gauge} {n : Side} {P : Rep G n}

/-- The complete marked forced-gas numerator, with its unmarked gas removed
as a constant polynomial.  Every mixed forced contribution remains. -/
def forcedClusterError (d : Deck R P) (U : Config G n) : Poly R :=
  d.contents.cluster U - (P.activities.gas P.p U : ℂ) • (1 : Poly R)

/-- The decomposition is an identity in the original unnormalized density. -/
theorem density_error_split (d : Deck R P) (U : Config G n) :
    d.density U - (P.eval U : ℂ) • (1 : Poly R) =
      (P.eval U : ℂ) • (Poly.pass (d.log U) - 1) +
      (Real.exp (P.exponent U) : ℂ) • (Poly.pass (d.log U) * forcedClusterError d U) := by
  unfold Deck.density forcedClusterError Rep.eval
  simp only [Complex.ofReal_mul, smul_sub, mul_sub, mul_smul_comm, mul_one, smul_smul]
  abel

omit [Fintype V] in
private theorem dominated_price {A : Poly R} {X : Type*} {F : X → Poly R}
    {w : V → ℝ} (hw : ∀ v, 0 < w v) (hp : Positive A) (hd : Dominates A F) (x : X) :
    Poly.price w (F x) ≤ Poly.price w A := by
  unfold Poly.price
  apply Finset.sum_le_sum
  intro s _
  rw [hp.norm]
  exact mul_le_mul_of_nonneg_left (hd x s) (Poly.worth hw s).le

variable {X : Type*} {o : V → Site n} {T : Taste X o P R} {p : BudgetPoint}
    {w cost : V → ℝ} {κ regularPrice forcedPrice : ℝ}

/-- A pointwise numerator estimate: the regular/caption contribution is
proved from FullBudget, and the untouched forced error is displayed exactly.
This statement makes no smallness claim about that final forced term. -/
theorem RelativeBudget.density_error_price
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) (hthreshold : p.threshold = P.p.threshold)
    (x : X) (U : Config G n) :
    Poly.price (fun v => w v / cost v)
      ((T.leaf x).density U - (P.eval U : ℂ) • (1 : Poly R)) ≤
      |P.eval U| * (Real.exp (Fintype.card V * regularPrice) - 1) +
      (Real.exp (P.exponent U) * Real.exp (Fintype.card V * regularPrice)) *
        Poly.price (fun v => w v / cost v) (forcedClusterError (T.leaf x) U) := by
  let a := fun v => w v / cost v
  have ha (v) : 0 < a v := div_pos (h.budget.radii v) (hcost v)
  obtain ⟨A, hp, hd, hb⟩ := h.physical_log_majorant hcost x hthreshold
  have hlog : Poly.price a ((T.leaf x).log U) ≤ Fintype.card V * regularPrice :=
    (dominated_price ha hp hd (x, U)).trans hb
  have hpass : Poly.price a (Poly.pass ((T.leaf x).log U)) ≤
      Real.exp (Fintype.card V * regularPrice) :=
    (Poly.pass_budget ha _).trans (Real.exp_monotone hlog)
  have htail : Poly.price a (Poly.pass ((T.leaf x).log U) - 1) ≤
      Real.exp (Fintype.card V * regularPrice) - 1 := by
    rw [pass_eq_one_add_tail, add_sub_cancel_left]
    exact (dominated_price ha hp.tail (hd.tail hp) (x, U)).trans
      ((tail_price_le hp ha).trans (sub_le_sub_right (Real.exp_monotone hb) 1))
  rw [density_error_split]
  apply (Poly.addition ha _ _).trans
  rw [Poly.adapted, Poly.adapted, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply add_le_add (mul_le_mul_of_nonneg_left htail (abs_nonneg _))
  exact (mul_le_mul_of_nonneg_left ((Poly.multiplication ha _ _).trans
    (mul_le_mul_of_nonneg_right hpass (Poly.nonnegative ha _))) (Real.exp_pos _).le).trans_eq
      (by ring)

/-- At an actual retained carrier, positivity comes from C.Makes and the
exact vacuum identity; no lower bound on the vacuum is postulated. -/
theorem carrier_eval_positive {C : Family G} {N period level : ℕ}
    (hC : C.Makes) (hlevel : level ≤ N) (Q : Carrier C N period level)
    (U : Config G (C.side level period)) : 0 < Q.rep.eval U := by
  rw [Q.vacuum]
  exact Multi.AxisShift.chosen_positive hC.wilson hlevel U

/-- Specialization of the numerator estimate to the same physical carrier.
All remaining work is the displayed forced-cluster numerator, not an
uncontrolled inverse physical density. -/
theorem actual_density_error_price {C : Family G} {N period level : ℕ}
    (hC : C.Makes) (hlevel : level ≤ N) (Q : Carrier C N period level)
    {o : V → Site (C.side level period)} {T : Taste X o Q.rep R}
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) (hthreshold : p.threshold = Q.rep.p.threshold)
    (x : X) (U : Config G (C.side level period)) :
    Poly.price (fun v => w v / cost v)
      ((T.leaf x).density U - (Q.rep.eval U : ℂ) • (1 : Poly R)) ≤
      Q.rep.eval U * (Real.exp (Fintype.card V * regularPrice) - 1) +
      (Real.exp (Q.rep.exponent U) * Real.exp (Fintype.card V * regularPrice)) *
        Poly.price (fun v => w v / cost v) (forcedClusterError (T.leaf x) U) := by
  simpa only [abs_of_pos (carrier_eval_positive hC hlevel Q U)] using
    h.density_error_price hcost hthreshold x U

end YM.Integration.LocalComparison
