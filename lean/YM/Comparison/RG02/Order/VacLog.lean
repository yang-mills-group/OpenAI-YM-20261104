import YM.Comparison.RG02.Order.Rim
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
/-!
# Vacuum logarithmic cost reader

Retain this as distinct from the marker-only logarithm when evaluating.
Compare at the true normalized table. Can diagnose one-step Retrait with **no truncation estimate
 on extensive polynomial invoked**; instead require a lower bound on the vacuum & use relative
 log displacement preserving cancellations. When one has the ball bounds for the vacuum-scalared
 Taylor extraction, use the other estimate `before`, with omitted(log) and natural log tail.
 Applies also to the actual Fk denominator. None of these inequalities alone asserts a working
 RG residual, or asymptotic even for the expressed log of one regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Order
open Function Finset MeasureTheory
open Marker Multi Join
open YM.Comparison.RG02.Cumulants
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub)
open scoped BigOperators Topology Classical
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

-- pure unmarked logarithm; holds up to r exactly, no higher-coupling terms dropped until rendering

def exponentPrice (x : Grade R r) (g : ℝ) := ((value (g:ℂ) (logVac x)).part R.quiet).re
lemma exponent_marked (x : Grade R r) (h : UnitLeading x) (hs : Simple x) (g : ℝ) :
    value (g:ℂ) (logVac x)=Poly.bead R (exponentPrice x g : ℂ) := by
   have he := at_value _ (log_color x hs h) g; unfold exponentPrice; rw [he.re]
   nth_rw 1 [← show denominator (logVac x)=logVac x from log_vacant h]; exact value_denom (logVac x) (g:ℂ)

lemma vacuum_prefix {x : Grade R r} (h : UnitLeading x) : logVac x=logTo r (denominator x) := by
    have ht : (projectRight R (indices r) x).part (indices r).quiet=1 := (rprojection_quiet ..).trans h
    unfold logVac denominator bottom; rw [AlgHom.comp_apply, ← log_map (injectRight R (indices r)) (inject_right_quiet _ _) ht, log_to _ ht r (order_limit r)]
    simp [logTo]

private lemma formula_log_omits (x : Grade R r) (h : UnitLeading x) (hx : Symmetric x) (g : ℂ) :
    logTo r (value g (denominator x)) = value g (logVac x) + omitted r g (logSeries r (render (denominator x))) := by
   rw [value_render g (denominator x),← formula_log,formula_omits r _ g,stamp_log,rerender (show Symmetric (denominator x) from hx.vacant),vacuum_prefix h]

/-- Sign variant with powers of `(1-v)` where v is the value of the unmarked Taylor through
 r. Natural log in final real protocol acts on the *actual* mass q, not the source-algebra unit. -/
def contour (v : ℝ) (r : ℕ) : ℝ := ∑ i∈range r,(1-v)^(i+1) / (i+1:ℕ)
def unmarked (x : Grade R r) (g : ℝ) := ((value (g:ℂ) x).part R.quiet).re
lemma pure_vacuum (x : Grade R r) (hs : Simple x) (g : ℝ) : Complex.ofReal (unmarked x g)=(value (g:ℂ) x).part R.quiet := (at_value x hs g).re

omit [Fintype V] in
private lemma mapped_log (w : ℂ) :
    logTo r (Poly.bead R w)=Poly.bead R (∑ i∈ range r, (-((↑(i+1) : ℂ))⁻¹)*(1-w)^(i+1)) := by
   rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_mul,map_pow,map_sub,map_one,Poly.product_bead]
lemma omissions (x : Grade R r) (h : UnitLeading x) (hx : Symmetric x) (hp : Simple x) (g : ℝ) :
    omitted r (g:ℂ) (logSeries r (render (denominator x)))=Poly.bead R (Complex.ofReal (-contour (unmarked x g) r - exponentPrice x g)) := by
    apply eq_sub_of_add_eq' (show value (↑g) (logVac x)+_=_ from (formula_log_omits x h hx g).symm) |>.trans
    rw [exponent_marked x h hp g,value_denom, ← pure_vacuum x hp g, mapped_log, ← map_sub, Complex.ofReal_sub]; unfold contour
    simp [Complex.ofReal_sum, div_eq_mul_inv, mul_comm (a:=(1- (unmarked x g:ℂ)) ^_), Finset.sum_neg_distrib]

lemma log_contour {g : ℝ} (h : |1-g| < 1) (n : ℕ) :
    |contour g n + Real.log g| ≤ |1-g|^(n+1)/(1-|1-g|) := by
   simpa only [contour,Nat.cast_succ, sub_sub_cancel] using Real.abs_log_sub_add_sum_range_le h n

lemma log_contrast {x y b : ℝ} (h : 0 < x) (he : 0 < y) (hp : b ≤ x) (hq : b ≤ y) : b*|Real.log x - Real.log y| ≤ |x-y| := by
   have hv {x y : ℝ} (h : 0 < x) (hx : b ≤ x) (hp : x ≤ y) : b*(Real.log y-Real.log x) ≤ y-x := by
      have hy : 0<y:= h.trans_le hp
      have hh : Real.log (y/x)=Real.log y-Real.log x:= Real.log_div hy.ne' h.ne'
      have hm : Real.log y-Real.log x ≤ y/x-1 := hh ▸ Real.log_le_sub_one_of_pos (div_pos hy h)
      calc
         _ ≤ x*(Real.log y-Real.log x) := mul_le_mul_of_nonneg_right hx (sub_nonneg.mpr (Real.log_le_log h hp))
         _ ≤ x*(y/x-1) := mul_le_mul_of_nonneg_left hm h.le
         _ = _ := by field_simp
   rcases le_total x y with h'|h'
   · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log h h')),abs_of_nonpos (sub_nonpos.mpr h'),neg_sub,neg_sub]; exact hv h hp h'
   rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log he h')),abs_of_nonneg (sub_nonneg.mpr h')]; exact hv he hq h'

lemma contour_bound (x : Grade R r) (h : UnitLeading x) (hx : Symmetric x) (hp : Simple x) (g z : ℝ) (hg : |g| ≤ z) (w : V→ℝ) (hw : ∀ i,0 < w i) :
    |- contour (unmarked x g) r - exponentPrice x g| ≤ |g|^(r+1)*subtotal w r z (logSeries r (render (denominator x))) := by
  have hp := tail_bound w hw r z (logSeries r (render (denominator x))) (g:ℂ) (by simpa using hg : ‖(g:ℂ)‖≤z)
  rw [omissions x h hx (by assumption)] at hp
  simpa [Poly.bead,-Complex.ofReal_sub,-Complex.ofReal_neg] using! hp
/-- Real log transport when q (rescaled real positive full contribution) is known additive-close
 and its denominator series stays away from zero via a |1-vac(...)|<1 budget. This
 estimate is a consumer, not uniform-in-volume or constants per phase/readouts. In bigger volume
 estimating only `q-exp(exponentPrice)` in a relative/additive norm *might* be better; irrespective
 of support-budget difficulties, `after` gives a supported-real-scalar cost on that same normalization.
 -/
lemma before (x : Grade R r) (h : UnitLeading x) (hx : Symmetric x) (hp : Simple x) (g z : ℝ) (hg : |g| ≤ z) (w : V→ℝ) (hw : ∀ i,0 < w i) (q b : ℝ) (hb : 0<b) (hs : |1-unmarked x g|<1) (hQ : b ≤ q) (hm : b ≤ unmarked x g) :
    b*|Real.log q - exponentPrice x g| ≤ |q-unmarked x g| + b*(|1-unmarked x g|^(r+1)/(1-|1-unmarked x g|) + |g|^(r+1)*subtotal w r z (logSeries r (render (denominator x)))) := by
   let v:=unmarked x g; let p:= exponentPrice x g; let l:=contour v r
   have he := log_contour hs r; have hw' := contour_bound x h hx hp g z hg w hw
   have H := show |Real.log q-p| ≤ |Real.log q-Real.log v| + (|l + Real.log v| + |-l-p|) from (by
     refine (Eq.le ?_).trans ((abs_add_le ..).trans (add_le_add le_rfl (abs_add_le ..))); congr 1; ring)
   calc
      _ ≤ b*(|Real.log q-Real.log v|+(|l+Real.log v|+|-l-p|)) := mul_le_mul_of_nonneg_left H hb.le
      _ ≤ _ := by rw [mul_add]; exact add_le_add (log_contrast (hb.trans_le hQ) (hb.trans_le hm) hQ hm) (mul_le_mul_of_nonneg_left (add_le_add he hw') hb.le)

lemma after (x : Grade R r) (g q b : ℝ) (hb : 0<b) (hs : b ≤ Real.exp (exponentPrice x g)) (hQ : b ≤ q) :
   b*|Real.log q - exponentPrice x g|≤ |q-Real.exp (exponentPrice x g)|:= by
   nth_rw 1 [← Real.log_exp (exponentPrice x g)]; exact log_contrast (hb.trans_le hQ) (Real.exp_pos _) hQ hs
end YM.Comparison.RG02.Order
