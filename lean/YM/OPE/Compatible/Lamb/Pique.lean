import YM.OPE.Compatible.Lamb.Stipe
/-! # Parsed log exponential service -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Zeph
open Function Filter Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree Push Push.AbsoluteSums Precision Matrix
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra GaussianScore Metric Limn
variable {G:Gauge}{c f:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin Set
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local Cascade Rill Glass Coin
variable {t r R B b ε x y z C k' R' t' t'' u:ℝ}{m:ℕ}
variable {S:StepData c f} {F: Forest S.ratio} {k:S.Choices}
local notation "Q" =>(Bid.Dir G c × AxisChart G F)
open Dew
lemma xpZ {x:ℝ}(h:‖x‖≤1): ‖Real.exp x-((1+x)+x^2/2)‖ ≤ ‖x‖^3:=by
       have hv:|Real.exp x-(1+x+x^2/2)| ≤ ‖x‖^3*((Nat.succ 3 : ℕ)/( ((3:ℕ).factorial:ℝ)* (↑(3:ℕ):ℝ))) :=by convert! Real.exp_bound h (n:=3) (by omega) using 2; norm_num [sum_range_succ]; try rfl
       refine hv.trans (mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) ?_); norm_num [Nat.factorial]
abbrev duesR (A:ℝ):= (2*A)^3+(3*A^2+A)
lemma grit_exp (ht:0<ε)(hb:ε≤1)(hx:‖y‖+‖z‖ ≤ t)(hh:‖x-(ε*y+ε^2*z)‖ ≤ t*ε^3)(hs:2*t*ε≤1): ‖Real.exp x-(1+ε*y+ε^2*(z+y^2/2))‖ ≤ duesR t*ε^3:=by
       have hv:0 ≤ t:=(add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hx; have hZ: ‖z‖ ≤ t:=(le_add_of_nonneg_left (norm_nonneg _)).trans hx; have hY:‖y‖ ≤ t:=(le_add_of_nonneg_right (norm_nonneg _)).trans hx; let f:= ε*y; let g:= x-(f+ε^2*z); have he: ‖f‖ ≤ ε*‖y‖:= le_of_eq (by unfold f; rw [norm_mul,Real.norm_of_nonneg ht.le]); have hp: ‖ε^2*z‖ ≤ ε^2*‖z‖:= le_of_eq (by rw [norm_mul,Real.norm_of_nonneg (by positivity)]); have h1: ‖x‖ ≤2*t*ε:=by
            rw [show x=g+(f+ε^2*z) by unfold g; ring]; apply (norm_add_le ..).trans; refine (add_le_add hh ((norm_add_le ..).trans (add_le_add he hp))).trans ?_
            have hT:ε^2≤ε:=by nlinarith
            have he: ε^3 ≤ ε:=by nlinarith [pow_pos ht 3]
            nlinarith only [mul_le_mul_of_nonneg_left hx ht.le,mul_le_mul_of_nonneg_left he hv,mul_le_mul_of_nonneg_right hT (norm_nonneg z)] -- rw x all!
       have hf : ‖f‖ ≤ ε*t:= he.trans (mul_le_mul_of_nonneg_left hY ht.le)
       have h2: ‖x-f‖ ≤2*t*ε^2:=by rw [show x-f=g+ε^2*z by unfold g;ring]; refine (norm_add_le ..).trans ((add_le_add hh (hp.trans (mul_le_mul_of_nonneg_left hZ (pow_nonneg ht.le _)))).trans ?_); calc
            _ ≤ t*(ε^2)+ε^2*t:= by have he': ε^3≤ ε^2:= (by rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg ht.le 2) hb); exact add_le_add (mul_le_mul_of_nonneg_left he' hv) le_rfl
            _ = _ := by ring
       have h3 : ‖(x-f)*(x+f)/2‖ ≤3*t^2*ε^3:=by
            rw[norm_div, Real.norm_of_nonneg (by norm_num : 0 ≤ (2:ℝ)), norm_mul]; refine (div_le_div_of_nonneg_right (mul_le_mul h2 ((norm_add_le ..).trans (add_le_add h1 hf)) (norm_nonneg _) (by positivity)) (by norm_num)).trans_eq ?_; ring
       rw [show Real.exp x-_=(Real.exp x-(1+x+x^2/2))+((x-f)*(x+f)/2+g) from (by unfold g f; ring)]; apply (norm_add_le ..).trans; apply (add_le_add ((xpZ (h1.trans hs)).trans (pow_le_pow_left₀ (norm_nonneg _) h1 _)) ((norm_add_le ..).trans (add_le_add h3 hh))).trans_eq; unfold duesR; ring
-- monotone under pp.LP uses norm. For PhysicalN condition
end YM.OPE.Zeph
