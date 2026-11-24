import YM.Integration.LocalComparisonForcedCover

/-!
Complete pointwise error bound in the original marked density.

The regular factor is paid by the factorial marked norm.  The entire forced
and mixed numerator is paid by the native compulsory-cover estimate, with
its original support reserve.  The remaining exponential background is
shown explicitly; this is not yet a volume-uniform normalized integral.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker RG3.Forms RG3.Script.Picnic SectorNext.Vacuum
open scoped Classical

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
    {G : Gauge} {n : Side} {P : Rep G n} {X : Type*}
    {o : V → Site n} {T : Taste X o P R} {p : BudgetPoint}
    {w cost : V → ℝ} {κ regularPrice forcedPrice : ℝ}

/-- All regular, forced and mixed coefficients are included. The final
factor keeps exact support on flagged configurations and the native
exponential decay in their full inventory. -/
theorem RelativeBudget.full_density_error_price
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) (hthreshold : p.threshold = P.p.threshold)
    {regular actualVacuum vacuum : ℝ}
    (hP : P.activities.Valid P.p regular actualVacuum)
    (hReserve : P.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    Poly.price (fun v => w v / cost v)
      ((T.leaf x).density U - (P.eval U : ℂ) • (1 : Poly R)) ≤
      |P.eval U| * (Real.exp (Fintype.card V * regularPrice) - 1) +
      (Real.exp (P.exponent U) * Real.exp (Fintype.card V * regularPrice)) *
        (if flags P.p.threshold U = ∅ then 0 else
          ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
            Real.exp (-flagRate p * (flags P.p.threshold U).card)) := by
  apply (h.density_error_price hcost hthreshold x U).trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left
    (h.forced_cluster_price_reserved_flagged hcost hP hReserve hSmall x U)
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)

/-- The same full bound on the retained actual physical carrier. No
pointwise lower bound on its gas or inverse vacuum is assumed. -/
theorem actual_full_density_error_price {C : Family G} {N period level : ℕ}
    (hC : C.Makes) (hlevel : level ≤ N) (Q : Carrier C N period level)
    {o : V → Site (C.side level period)} {T : Taste X o Q.rep R}
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) (hthreshold : p.threshold = Q.rep.p.threshold)
    {regular actualVacuum vacuum : ℝ}
    (hP : Q.rep.activities.Valid Q.rep.p regular actualVacuum)
    (hReserve : Q.rep.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G (C.side level period)) :
    Poly.price (fun v => w v / cost v)
      ((T.leaf x).density U - (Q.rep.eval U : ℂ) • (1 : Poly R)) ≤
      Q.rep.eval U * (Real.exp (Fintype.card V * regularPrice) - 1) +
      (Real.exp (Q.rep.exponent U) * Real.exp (Fintype.card V * regularPrice)) *
        (if flags Q.rep.p.threshold U = ∅ then 0 else
          ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
            Real.exp (-flagRate p * (flags Q.rep.p.threshold U).card)) := by
  simpa only [abs_of_pos (carrier_eval_positive hC hlevel Q U)] using
    h.full_density_error_price hcost hthreshold hP hReserve hSmall x U

end YM.Integration.LocalComparison
