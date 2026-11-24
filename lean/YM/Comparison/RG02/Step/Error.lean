import YM.Comparison.RG02.Integral.Comparison
import YM.Comparison.RG02.Normal.Tagged
import YM.Comparison.RG02.Bulk.Spur
import YM.Comparison.RG02.Order.VacLog
/-!
# One-step normalization and explicit error reader

Keep per-torus volumes everywhere. Includes the log conventions in `Kernel` and explicit
 use of `Bulk.Fk` projected to THIS `r`. Does *not* claim weighted cost estimates on the analytic
 representation -- input/output Density budgets E & marks are not this numerical Poly.price
 alone. Useful to charge exact `Window` costs separately on a virtual-period statement, etc (read
 only on THAT same period). In particular cannot assume global price of a massive-volume Taylor
 remainder or its per-volume variant is small from small normalized/corner/marginal errors.
 Tail(weighted actual RG budget) OPEN in other tasks. This module supplies normalization algebra
 at those estimates; costs as pointwise Marked moment on *THIS* coarse configuration* only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Local
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open YM.Marker YM.Multi Order Integral Actual
open Normal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {c f : Side} {S : StepData c f} {O : ChartRatio G}
    {V : Type} [DecidableEq V] [Fintype V] {C : Census V} -- marker census

variable (R : Rep G f) (X : Lit C (Config G f)) (K : Bulk.Kernel S R.clip R.path O) (g : ℝ)
    (F : Forest S.ratio) (t : S.Choices)
    (W : Bulk.Colors C G f) (A : S.Choices → Set (F.Slice G)) (x : fieldDir G c 1) (r : ℕ)
local notation "F'"=> Bulk.Fk K F t W x r
local notation "S'"=> office K F t g (levelScalar R) x
local notation "V'"=> sample g x

def yield (S : StepData c f) (J : Config G c) := Actual.Push S R.beta X J
-- denominator unnormalized actual.
def settled (S : StepData c f) (J : Config G c) := S.push R.beta R.eval J
local notation "Y"=> yield R X S V'
local notation "d"=> settled R S V'

def normalized (S : StepData c f) (J : Config G c) := Order.unitScale (yield R X S J)
def cumulant (S : StepData c f) (J : Config G c) := Extra.Trajectories.connected (normalized R X S J)
local notation "N"=> normalized R X S V'
local notation "y" => (S' : ℂ)

def money := (S')⁻¹*d

def sized := (y)⁻¹ • Y
def pixels := (y)⁻¹ • leftover K F g (levelScalar R) x W X r A -- arg order later

-- estimated denominators at actual fixed coarse J not assumed. Need small threshold slices;
-- here exact, full. `token` receipt includes all costs needed only for actual integral identity
-- (not qev etc); `W` not product estimates. Instantiate with supplied `Kernel` & W, optionally
-- supplement inherited E.
variable {X}
structure Opened (R : Rep G f) (K : Bulk.Kernel S R.clip R.path O) (X : Lit C (Config G f)) (g : ℝ) (W : Bulk.Colors C G f) : Prop where
    fine : Floor R X
    strong : Strong f R.eval
    kin : Bulk.Well W
    eye : 0 < g
    beta : R.beta=temperature g

namespace Opened
variable {R K g W}
variable (L : Opened R K X g W)
include L
omit [Fintype V] in
lemma settled_pos (J : Config G c) : 0<settled R S J := Normal.total_pos S R.beta J R.eval L.strong K.branches
omit [Fintype V] in
lemma uncramped (J : Config G c) : (yield R X S J).part C.quiet=Complex.ofReal (settled R S J) := by rw [yield, ← Normal.scan_actual S R.beta J X K.branches L.fine.safe]; exact Normal.scan_bare S R.beta J _ R.eval L.strong K.branches (fun _=>L.fine.vacancy)
omit [Fintype V] in
lemma settles (J : Config G c) : normalized R X S J=(Complex.ofReal (settled R S J))⁻¹ • yield R X S J := by rw [normalized, Order.unitScale, L.uncramped]
omit [Fintype V] in
lemma none_zero (J : Config G c) : (yield R X S J).part C.quiet≠0 := by rw [L.uncramped]; exact_mod_cast (L.settled_pos J).ne'
omit [Fintype V] in
lemma pays (J : Config G c) : Complex.ofReal (settled R S J) • normalized R X S J=yield R X S J := by rw [← L.uncramped J]; exact scale_value (L.none_zero J)
omit [Fintype V] in
lemma money_pos : 0 < money R K g F t x := mul_pos (inv_pos.mpr (office_pos K F t g _ x L.eye)) (L.settled_pos _)
omit [Fintype V] in
lemma size_price : (sized R X K g F t x).part C.quiet= Complex.ofReal (money R K g F t x) := by unfold sized money; rw [Poly.part_smul,L.uncramped, Complex.ofReal_mul,Complex.ofReal_inv]
omit [Fintype V] in
lemma coins : (y)≠0 := by exact_mod_cast (office_pos K F t g (levelScalar R) x L.eye).ne'
omit [Fintype V] in
lemma main_cost : N=Order.unitScale (sized R X K g F t x) := (Order.scaled_same (Y) (y)⁻¹ (inv_ne_zero (L.coins F t x))).symm
omit [Fintype V] in
lemma paid_as (J : Config G c) : Order.unitScale (Normal.scan S R.beta J (fun _=> X))=normalized R X S J := by rw [Normal.scan_actual S R.beta J X K.branches L.fine.safe]; rfl

variable (h : ∀ t, Trust K F t g x (A t)) -- consumer may need stronger mask etc.
include h
local notation "M"=> money R K g F t x
local notation "S!"=> sized R X K g F t x
local notation "E"=> pixels R X K g F t W A x r
local notation "H"=> value (g:ℂ) F'
local notation "Q"=> value (g:ℂ) (Order.ratio (F'))
local notation "U"=> M
local notation "q₀"=> Local.cumulant R X S V'
local notation "L'"=> value (g:ℂ) (logMarked (F'))

/-- Connection of the exact denominator to Fk's polynomial. Not claiming it stays near 1
    uniformly. -/
lemma size_formula : S! = H + E := by
   unfold sized pixels yield; rw [L.beta, Integral.compare K F t g (levelScalar R) x W X r L.eye L.kin L.fine.safe A h L.fine.gauges]; rw [smul_add,smul_smul,inv_mul_cancel₀ (L.coins F t x),one_smul]
lemma money_total : M = unmarked (F') g + ((E).part C.quiet).re := by
   rw [← Complex.ofReal_re M,← L.size_price F t x,L.size_formula F t A x r h]; unfold unmarked; simp
lemma ratio_residual : Complex.ofReal U • (N-Q) = E - (E).part C.quiet • Q - omitted r (g:ℂ) (render (denominator (F')) * render (Order.ratio (F'))) := by
    have he := L.size_price F t x
    rw [← he, L.main_cost F t x, ← scaled_reconstruct (show (S!).part C.quiet≠0 by rw [he]; exact_mod_cast (L.money_pos F t x).ne')]; apply ratio_defect (Bulk.fk_unit ..) (Bulk.fk_sym ..) (g:ℂ) (S!) (E) (L.size_formula F t A x r h)

omit L h in
lemma full_cost (n : ℕ) (H' : ∀ j:C.Mode,j.val.card≤n) :
    q₀ - L' = Extra.Trajectories.connected N - Extra.Trajectories.connected Q +
      omitted r (g:ℂ) (logSeries (n+r) (render (Order.ratio (F')))) := by rw [log_mark_defect (Bulk.fk_unit ..) (Bulk.fk_sym ..) _ n H']; unfold Local.cumulant; abel

-- Pointwise costs supporting valuation/denominator necessities. Some hypotheses here may not
-- be useful uniformly (e.g. triangle inequality on cross-product/global denominator). Stronger
-- supported norm extraction open, use exact `size_formula` and logarithmic re-expressions.
variable (z b : ℝ) (w : V→ℝ)
lemma pays_ratio (hm : |g|≤z) (hb : b≤ M) (hw : ∀ i, 0 < w i) :
    b* Poly.price w (N-Q) ≤ Poly.price w (E-(E).part C.quiet • Q) + g^(r+1)*subtotal w r z (render (denominator (F')) *render (Order.ratio (F'))) := by
   rw [L.main_cost F t x]; have he : ‖(S!|>.part C.quiet)‖=M := by rw [L.size_price F t x]; simp [(L.money_pos F t x).le]
   have HN : ‖(g:ℂ)‖=g := by simp [L.eye.le]
   have hq := ratio_pay (Bulk.fk_unit K F t W x r) (Bulk.fk_sym ..) (g:ℂ) (by simpa using hm : ‖(g:ℂ)‖ ≤ z) _ _ (by rw [L.size_price F t x]; exact_mod_cast (L.money_pos F t x).ne') (L.size_formula F t A x r h) (he.symm ▸ hb) w hw
   rwa [HN] at hq
omit h in
lemma pays_log (hm : |g|≤z) (n : ℕ) (H' : ∀ j:C.Mode,j.val.card ≤ n) (hw : ∀ i,0 < w i) (B : ℝ) (he : Poly.price w (1-N) ≤ B) (hx : Poly.price w (1-Q)≤B) :
    Poly.price w (q₀-L') ≤ repeats n B * Poly.price w (N-Q)+ g^(r+1)*subtotal w r z (logSeries (n+r) (render (Order.ratio (F')))) := by
   have hq := log_mark_pay (Bulk.fk_unit ..) (Bulk.fk_sym ..) (g:ℂ) (by simpa using hm : ‖(g:ℂ)‖ ≤ z) n H' (Y) (L.none_zero _) w hw he hx (le_refl _)
   have hu : ‖(g:ℂ)‖=g := by simp [L.eye.le]
   simpa only [Local.normalized,Local.cumulant,hu] using hq

lemma pays_abs (hm : |g|≤z) (hu : b ≤ M) (hb : 0<b) (hw : ∀ i, 0<w i) (hn : |1-unmarked F' g|<1) (h₀ : b ≤ unmarked F' g) :
     b * |Real.log M - exponentPrice F' g| ≤ |((E).part C.quiet).re| + b*(|1-unmarked F' g|^(r+1)/(1-|1-unmarked F' g|)+|g|^(r+1)*subtotal w r z (logSeries r (render (denominator F')))) := by
   have hs := before (F') (Bulk.fk_unit ..) (Bulk.fk_sym ..) (Bulk.uncolored K F t W x r) g z hm w hw M b hb hn hu h₀
   rwa [show M-unmarked F' g = _ from sub_eq_iff_eq_add'.mpr (L.money_total F t A x r h)] at hs
lemma pays_relative (hu : b ≤ M) (hb : 0<b) (hm : b ≤ Real.exp (exponentPrice F' g)) : b * |Real.log M - exponentPrice F' g| ≤ |unmarked F' g + ((E).part C.quiet).re- Real.exp (exponentPrice F' g)|  := by rw [← L.money_total F t A x r h]; exact after F' g M b hb hm hu
end Opened
end YM.Comparison.RG02.Local
