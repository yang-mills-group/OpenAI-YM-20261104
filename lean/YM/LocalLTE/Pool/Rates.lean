import YM.LocalLTE.Pool.Port
/-! # Boundary surface payments on same theory. Extra regular stencil tags; hail projection and rotate. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Frost
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open AnalyticBridge VerifiedReset Collection Price
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf Urns
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
open Start Animals
open Padded Ovens Pipes
variable {x t :ℝ} (M:ℕ) {κ k:ℝ} (p: BudgetPoint)(c:Clip)
open Topology Timing 
open Real (log exp)
open Payments RG.Shoot
variable (A:Stage) (η:ℝ) (L:Side)
-- s = log x
lemma sameCost (q:BudgetPoint) (A:Stage)(hP: q.supportExponent=A.supportExponent) : Frost.kettleP q M η=kettleP (Time.probe A) M η ∧ Frost.chum q= Frost.chum (Time.probe A):= by unfold chum kettleP; rw [hP]; exact ⟨rfl,rfl⟩
lemma ray_p : Rate G L 1 id:= Rate.hat.compare (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t h; change |t|≤|betaF G t L|; rw [abs_of_pos h]; exact (le_add_of_nonneg_right (Work.E04.shift_nonneg ..)).trans (le_abs_self _))
include L
lemma pay_ink (he:η>0): ∀ᶠ x:ℝ in atTop,∀ q:BudgetPoint,q.order=A.order→q.power=A.power→ q.threshold=Pressure.temp x→ q.threshold ≤2*Pressure.fiery G x L→ 2*x*Start.item G q≤η*x^chip 0:=by
    let f(x:ℝ):=2*x*(Start.price G A.order A.power *((2*Pressure.fiery G x L)^ (5:ℕ)))
    have hx: Rate G L (-(3:ℝ)/2) f:= by
       unfold f; convert (((Frost.ray_p G L).mul_left 2).mul (((Rate.flame (G:=G) (L:=L)|>.mul_left 2).pow 5).mul_left (Start.price G A.order A.power))) using 1; norm_num; rfl
    filter_upwards [Sienna.contraction G L (a:=1) he hx (show (-(3:ℝ)/2) < chip 0 by norm_num [chip]),eventually_gt_atTop (0:ℝ)] with x h hz q hQ hP ht hh; let t:= betaF G x L
    have hh' : 2*x* Start.item G q ≤ f x := by unfold item f; rw [hQ,hP]; have he:=q.threshold_pos; have hv:=(Start.constants G A.order A.power).1; gcongr
    apply hh'.trans; rw [one_mul] at h; exact h.le.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hz (le_add_of_nonneg_right (Work.E04.shift_nonneg ..)) (show chip 0≤0 by norm_num [chip])) he.le)
lemma pay_shelf (j:ℕ)(he:η>0): ∀ᶠ x:ℝ in atTop, ∀ q:BudgetPoint,q.order=A.order→q.power=A.power→2*x*(turnFee q * (betaF G x L)^(Urns.dust j-1)) ≤ η*x^chip (j+1):=by
    let P:=Time.probe A; let s:=turnFee P; let f x:=2*x*(s*((betaF G x L)^(Urns.dust j-1)))
    have h:Rate G L (Urns.dust j) f:= by
       convert (((Frost.ray_p G L).mul_left 2).mul ((Rate.power (G:=G) (L:=L) (a:= Urns.dust j-1)).mul_left s)) using 1; ring; rfl
    filter_upwards [Sienna.contraction G L (a:=1) he h (show Urns.dust j<chip (j+1) by unfold Urns.dust; linarith),eventually_gt_atTop (0:ℝ)] with x hx hz q hq hu
    rw [show turnFee q=s from ?_]; rw [one_mul] at hx; exact hx.le.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hz (le_add_of_nonneg_right (Work.E04.shift_nonneg ..)) (show chip (j+1) ≤0 by unfold chip; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) j])) he.le)
    unfold s turnFee P; rw [hq,hu]; rfl
end YM.WilsonStartup.Frost
