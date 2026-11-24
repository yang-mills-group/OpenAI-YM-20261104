import YM.Comparison.RG02.Step.Error
/-!
# Real one-step algebra reconstructed log

The local Fk answer plus named mask/window/chart costs on the Fiber.
`receipt` re-expresses actual FULL density at this V and g (in log
 form with the entire scalar). Treat this as statement of what canonical coefficients (whole
 Fk.answer, traced scalar and marked log by same conditional normalization and same scale) to
 render when forming the localized real regular and forced estimates. Doesn't say
 this particular split into additive pieces, or ANY representation, has incurred only small/support
 costs. In particular **do not** take a price norm of `moment defect` and infer a weighted norm on
 older representation (likely estimating in physical torus absolute moment or log without
 comparing first in a suitable regularized region & canonical address basis would be useless).
 `delay` here physiological D may itself be exponentially small or enormous in volume. `Opened`
 contains no assertions of asymptotics. The positivity premise is verified on same step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Local
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open YM.Marker YM.Multi Order Integral Actual
open YM.Extra.Trajectories (connected pass_connected connected_quiet)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {O : ChartRatio G}
    {V : Type} [DecidableEq V] [Fintype V] {C : Census V}
variable (R : Rep G f) (X : Lit C (Config G f)) (K : Bulk.Kernel S R.clip R.path O) (g : ℝ)
    (F : Forest S.ratio) (t : S.Choices) (W : Bulk.Colors C G f)
    (A : S.Choices → Set (F.Slice G)) (x : fieldDir G c 1) (r : ℕ)
local notation "F'"=> Bulk.Fk K F t W x r
local notation "S'"=> office K F t g (levelScalar R) x
local notation "V'"=> sample g x
local notation "E"=> pixels R X K g F t W A x r
local notation "Q"=> value (g:ℂ) (Order.ratio (F'))
local notation "L'"=> value (g:ℂ) (logMarked (F'))
local notation "P'"=> exponentPrice (F') g

-- quantity snapshots for cost readers (these definitions have no exact output inside on lhs)
def proceed := unmarked (F') g + ((E).part C.quiet).re
def vacuumError := Real.log (proceed R X K g F t W A x r)-P'
def normalizeError := (Complex.ofReal (proceed R X K g F t W A x r))⁻¹ •
    (E - (E).part C.quiet • Q - omitted r (g:ℂ) (render (denominator (F')) * render (Order.ratio (F'))))

def markingError (a : ℕ) := connected (Q+normalizeError R X K g F t W A x r)-connected Q +
     omitted r (g:ℂ) (logSeries (a+r) (render (Order.ratio (F'))))
local notation "e"=>vacuumError R X K g F t W A x r
local notation "δ"=>normalizeError R X K g F t W A x r
local notation "ζ"=>markingError R X K g F t W A x r
local notation "sU" => proceed R X K g F t W A x r
local notation "N"=> normalized R X S V'
local notation "Y"=> yield R X S V'
namespace Opened
variable {R K g X W}
variable (Lh : Opened R K X g W)
    (hA : ∀ t, MeasurableSet (A t)) (HX : ∀ t, A t⊆zone K R.p F g x)
include hA HX
lemma trustworthy (θ : S.Choices): Trust K F θ g x (A θ) := limited K F _ _ _ θ _ (HX θ) (hA θ)
local notation "ht"=> trustworthy F A x hA HX
include Lh
lemma can_proceed : 0<sU := by unfold proceed; rw [← Lh.money_total F t A x r ht]; exact Lh.money_pos F t x
lemma unmarked_price : settled R S V' = S' * Real.exp (P'+e) := by
   unfold vacuumError; rw [add_sub_cancel, Real.exp_log (Lh.can_proceed F t A x r hA HX),proceed, ← Lh.money_total F t A x r ht, money, mul_inv_cancel_left₀ (office_pos K F t g (levelScalar R) x Lh.eye).ne']
lemma normalized_eq : N = Q + δ := by
   unfold normalizeError proceed; rw [← Lh.money_total F t A x r ht, ← Lh.ratio_residual F t A x r ht, smul_smul, inv_mul_cancel₀ (show (↑(money R K g F t x) : ℂ)≠0 from Complex.ofReal_ne_zero.mpr (Lh.money_pos F t x).ne'),one_smul]; abel

variable (n : ℕ) (H' : ∀ j:C.Mode,j.val.card≤n)
include H'
lemma marked_eq : Local.cumulant R X S V' = L' + ζ n := by
   unfold markingError; rw [← Lh.normalized_eq F t A x r hA HX, ← Opened.full_cost F t x r n H']; abel
lemma receipt :
   Local.yield R X S V'= Complex.ofReal (S' * Real.exp (P'+e)) • Poly.pass (L' + ζ n) := by
   rw [← Lh.unmarked_price F t A x r hA HX, ← Lh.marked_eq F t A x r hA HX n H', Local.cumulant, pass_connected (show (N).part C.quiet=1 from unitScore (Lh.none_zero V')), Lh.pays V']

/-- For estimating the costs, optionally use these additional hypotheses of physically paid
 bills. They are structured as bounds on known pieces (may hold only after localizing and on
 normalized letters, not asserted here). Not requiring that `e` & `ζ` themselves are small to
 declare this identity; log-costs follow from the shared positive denominator and truncation.
 Use as consumers before the actual represented budgets -- scaling powers etc. To feed the
 shared Clause B and estimate a mask/announcement budget from these pointwise costs needs OTHER
 theorems; no such statement is implied by the theorem below. -/
lemma bills (z b : ℝ) (w : V→ℝ) (M : ℝ) (hm : |g|≤z) (hb : 0<b)
    (he : b ≤ sU) (hs : b ≤ Real.exp P') (hw : ∀ i, 0 < w i)
    (hN : Poly.price w (1-Q) ≤ M) (hK : Poly.price w (1-N) ≤ M) :
    b*|e| ≤ |sU-Real.exp P'| ∧
    Poly.price w δ ≤ (Poly.price w (E-(E).part C.quiet • Q) + g^(r+1) * subtotal w r z (render (denominator (F')) * render (Order.ratio (F'))))/b ∧
    Poly.price w (ζ n) ≤ repeats n M * Poly.price w δ + g^(r+1)* subtotal w r z (logSeries (n+r) (render (Order.ratio (F')))) := by
   have hd : proceed R X K g F t W A x r = money R K g F t x:= (Lh.money_total F t A x r ht).symm
   have hD:b ≤ money R K g F t x:= hd ▸ he
   have hu : δ = N - Q:= by rw [Lh.normalized_eq F t A x r hA HX]; abel
   have hv : ζ n= Local.cumulant R X S V' - L':= by rw [Lh.marked_eq F t A x r hA HX n H']; abel
   rw [hu,hv]; refine ⟨Order.after F' g sU b hb hs he, (le_div_iff₀ hb).2 ?_,Lh.pays_log F t x r z w hm n H' hw M hK hN⟩
   rw [mul_comm]; exact Lh.pays_ratio F t A x r ht z b w hm hD hw
end Opened
end YM.Comparison.RG02.Local
