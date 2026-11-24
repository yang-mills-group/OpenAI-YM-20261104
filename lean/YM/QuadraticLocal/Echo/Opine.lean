import YM.QuadraticLocal.Echo.Spot
import YM.AllOrder.Wheel.Berth
/-! `MatchingR2` has a related estimate at its lamp `Zh`. Here on TRUE chart.L.Area.H
 Numeric materialization.Loc.S.St only invocation analyst.Need preserve entire tree.Placeholders. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Echo
open Function Filter Lattice Laurent Wilson RG Pressure Input Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Stationary
open MeasureTheory AllOrder.Floe
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
open Aperture Poetry
variable {ι V : Type}[Fintype V][DecidableEq V]{G:Gauge}{n:Side} (q:V)(W:V→ Site n)(L : Roll G V)
variable {k j e d:ℕ}{a σ Z τ A:ℝ}
namespace Trace
local notation "X"=> Apex n G
open Gauge Work.F02
-- uniform A-clamped analytic pole. Sup-budget Site.B.Root outside this.Cost book reexpression.Actor.
private def epoch (G:Gauge)(n:Side) := tint G (Exterior.Body 1 n)
lemma hill_bill (P:PaintSupply G k A)(x:Apex n G)(h:‖x‖≤1)(i:Edge (Site n)): Allows k (fun y=> G.mat (Desk.night y i)) x (fineCost G k A):=by
   let Z:= (ContinuousLinearMap.proj («φ»:=fun _ : Exterior.Body 1 n=>G.Color) (R:=ℝ) (i.1,coord i.2)).comp (epoch G n).toContinuousLinearMap; let A':= Uniform.shade G; have hp:0<A':=shade_pos _; have hv: ‖Z‖≤A':= Z.opNorm_le_bound hp.le fun v=> (norm_le_pi_norm (epoch G n v) _).trans (tint_le v); have he: ‖Z x‖≤A':=(Z.le_opNorm _).trans ((mul_le_mul hv h (norm_nonneg _) hp.le).trans_eq (mul_one A')); simp_rw [Desk.night,Work.F03.represent_link]
   refine ((P.2 _ he).comp (f:=Z) (allows_linear hv he)|>.mono ?_); have ht:=(outer_pos G k P.1).le; unfold fineCost; let B:=outerCost G k A+‖(1:G.Mat)‖; refine le_trans (show outerCost G k A ≤ B from le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_right ?_); change 0≤2^k*B*B; unfold B; positivity
abbrev branch (G:Gauge) (A σ:ℝ) (n k:ℕ):= pathPrice G A (2*σ) n * |slotConst G| ^ k
def setX (q:Atom G j)(x:Site n)(z:Apex n G): ℝ:= q.unmasked (Desk.night z) x
lemma allows (hp:0<σ)(hh:PaintSupply G k A)(x:Apex n G)(hx:‖x‖ ≤ 1)(q:Atom G j)(z:Site n): Allows k (setX q z) x (q.budget σ*branch G A σ k j):= by
   let U:= Desk.night (c:=n) (G:=G); let P:= (fun z=> physical (U z)); let m:=σ; have hy:0≤ q.magnitude:=by unfold Atom.magnitude; positivity
   have hE := Push.Uniform.allows_real_of_entire k (atomExt_contDiff q z) (x:=P x) (radius_pos hp) (fun y he=> (atomExt_bound q (U x) hp y (Metric.ball_subset_closedBall he) z).trans (show _≤q.budget m*|slotConst G| ^ j from ?_)); swap;
   · by_cases h:0≤ slotConst G; · rw [abs_of_nonneg h]
     apply mul_le_mul_of_nonneg_left _ (mul_nonneg hy (Real.exp_pos _).le); rw [← abs_pow]; exact le_abs_self _
   have ht:= hE.comp (f:=P) (Push.Uniform.allows_ambient (U:=U) (hill_bill hh x hx)); have he: ∀ y,setX q z y=Complex.reCLM (atomExt q z (P y)):=by intro y; unfold P setX; rw [atomExt_physical]; rfl
   rw [funext he]; exact ((ht.linear Complex.reCLM Complex.reCLM_norm.le)).mono (le_of_eq (by unfold m branch pathPrice Push.Uniform.composeCost; rw [show 2*σ/2=σ from by ring]; ring)) -- x-cost
-- stronger geom uses Lantern.length charged.Shape.Pap.A
variable (F:Poetry.Lantern G V)(x:Apex n G)(he:0<σ)(hp:PaintSupply G k A)(y:Site n)
local notation "T"=> F.money σ
include he hp
lemma cash (hx:‖x‖≤1): Allows k (setX F.atom y) x (F.money σ*branch G A σ k F.r):= by
 refine (allows he hp _ hx _ _).mono ?_; gcongr; · unfold branch; have hv: 0 ≤ pathPrice G A (2*σ) k:=(pathPrice_pos hp (mul_pos (by norm_num) he)).le; positivity
 exact Spot.monitor F _ he.le
end Trace
end YM.QuadraticLocal.Echo
