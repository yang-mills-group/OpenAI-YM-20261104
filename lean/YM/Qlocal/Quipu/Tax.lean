import YM.Qlocal.Quipu.Stem
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tint
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Engrave
import YM.Extra.ITERATION_NO_LOSS.Sums
/-!
 lease Modal. Long tails before splitting. Keep polynomial-in-momentum costs, allowing caller to charge from **true unmasked exponential** path envelope. Marker support weights (at late proof) different units. Receipt via full group toll; extension to complex neighborhood.B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet.Vase
open Function Filter Lattice Laurent RG Wilson Stationary Lasso Zora Work.F02 Metric
open Marker Multi Finset
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze ConnectedActivityE6
variable {V:Type}[DecidableEq V]{ι E:Type} {G:Gauge}{k n j r i:ℕ} {c:Side} {d t a v u C:ℝ}{R:Census V}
local notation "Ω"=> G.Color
variable (s':V→Site c) {s:Senses R}(A:Vase s G n)(x:Site c)(W:Config G c)
-- `Reach304`: price as `(1+length)^k` G constant basis.Tensor
private lemma timely (G:Gauge)(k t:ℕ) :∃ v:ℝ,0≤v ∧ ∀ (x:G.Color), ‖x‖≤1→ Brush k v 1 (theta G t) x := by
 obtain ⟨v,hc,hV⟩:= Brush.compact (s:= Metric.closedBall (0:G.Color) 1) (isCompact_closedBall _ _) (fun i _=> ((theta_cont G t).contDiffAt).of_le (show _ from le_top (a:= (↑k:WithTop ℕ∞)))) -- local notation bug Ω capital G
 exact ⟨v,hc.le,fun i hi=> hV i (mem_closedBall_zero_iff.mpr hi)⟩
def rate (G:Gauge) (k t:ℕ):= (1:ℝ)+k.factorial*(timely G k t).choose
lemma rated (G:Gauge)(k t:ℕ):1≤rate G k t:=le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (timely ..).choose_spec.1)
local notation "v₀[" t "]"=>rate G k t
lemma covered (j:Fin n): ((A.maps j).range+(A.maps j).tour.length) ≤ A.momentum:= Nat.le_trans (single_le_sum (f:=fun i:Fin n=>(A.maps i).range+(A.maps i).tour.length) (fun i _=> Nat.zero_le _) (mem_univ j)) (Nat.le_add_right ..)
section smooth
variable [NormedAddCommGroup E][NormedSpace ℝ E] {y:E}{U:E → Config G c}(hu:Mode U y k d)
local notation "Z"=> 2*(d*royalty G)
def velocity (G:Gauge)(p:ℕ) (d:ℝ):= (1:ℝ)*p*(2*(d*royalty G))
local notation "w"=> velocity G A.momentum d
include hu
lemma amended (j:Fin n)(t:ℕ): Brush k (rate G k t) (velocity G A.momentum d) (fun z=> amend G t (A.tan j) (travel (U z) x (A.maps j).tour)) y:= by
 let w₀ := (A.maps j).tour; let ℓ:ℝ:= w₀.length; let v:=d*royalty G; let u z:= travel (U z) x w₀
 have hm := sculpt (g:=u) (tour w₀ x hu.pos hu.atLink); have hx:0≤ v:=mul_nonneg hu.pos (zero_le_one.trans (royalty_ge ..)); have he: ℓ*v≤ A.momentum*v:=mul_le_mul_of_nonneg_right (by unfold ℓ; exact_mod_cast (show w₀.length ≤ A.momentum from (Nat.le_add_left ..).trans (A.covered j))) hx
 have hl:ℓ*v ≥ 0:=mul_nonneg (Nat.cast_nonneg _) hx
 unfold amend; split
 next hi => refine (hm.pine ((timely G k t).choose_spec.2 _ hm.bound)).climb (le_add_of_nonneg_left zero_le_one) ?_; unfold velocity; change (1+1:ℝ)*(ℓ*v)≤ 1*A.momentum*(2*v); linarith only [he]
 refine hm.climb (rated G k t) ?_; unfold velocity; change ℓ*v≤ (1*A.momentum*(2*v):ℝ); linarith only [he,hl]
abbrev toll (G:Gauge) (n t k:ℕ) (d:ℝ)(x:ℕ) := ((rate G k t)^n) * (1+n* velocity G x d)^k
omit hu in
lemma toll_core (G:Gauge)(n t k:ℕ){d:ℝ}(hd:0 ≤ d)(x:ℕ):0≤toll G n t k d x:= by unfold toll velocity; have hc:=royalty_ge G; have hr:=rated G k t; positivity
lemma glorious (t:ℕ): Brush k (A.sizeC*toll G n t k d A.momentum) 1 (A.read x t ∘ U) y:= by
 let v:=rate G k t; let X(i:Fin n)(y:E) := amend G t (A.tan i) (travel (U y) x (A.maps i).tour); let u (b: Ink G n)(y:E):= ∏ i:Fin n, X i y (b i); have ht (b:Ink G n): Brush k (v^n) (n*w) (u b) y := by
     simpa [v, u] using! (Brush.all_prod (univ: Finset (Fin n)) _ (fun _=>rate G k t) (fun _=>w) (fun i _=> colorEvaluated (b i) (amended A x hu i t))) -- w notation simp issue
 have hh:0 ≤ (n*w:ℝ):= by unfold velocity; have he:= hu.pos; have hx:= royalty_ge G; positivity
 have hF:= Brush.spree Finset.univ _ _ hh (fun i _=> (ht i).smul (A.ink i)); rw [← Finset.sum_mul] at hF; rw [show A.read x t ∘ U=(fun y:E=>∑ i:Ink G n,A.ink i • u i y) from funext fun y=> A.globe x (U y) t]; exact hF.trim.climb (le_of_eq (mul_assoc ..)) le_rfl
omit hu
open Extra.Iteration
lemma late (G:Gauge)(d:ℝ)(hd:0≤d)(n t k:ℕ)(i:ℕ) : toll G n t k d i ≤ toll G n t k d 1 * (1+i:ℝ)^k := by
 unfold toll velocity; push_cast; rw [mul_assoc ((rate G k t)^n),← mul_pow]; refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ _) (pow_nonneg (zero_le_one.trans (rated ..)) n) -- n not k
 · have hh:=royalty_ge G; positivity
 have he:0≤ royalty G:= zero_le_one.trans (royalty_ge _); nlinarith [show 0≤ (i:ℝ) from Nat.cast_nonneg _,show 0≤ (n:ℝ)*(d*royalty G) from by positivity]
def capita (G:Gauge)(n t k:ℕ) (d a:ℝ):= toll G n t k d 1 * momentPrice k a
lemma capita_ge (G:Gauge)(n t k:ℕ) {d a:ℝ}(hd:0≤d)(ha:0<a):0≤capita G n t k d a:= mul_nonneg (toll_core G _ _ _ hd _) (momentPrice_pos _ ha).le
include hu
lemma palace(t:ℕ)(ha:0<a): Brush k (capita G n t k d a*A.fare a) 1 (A.read x t ∘ U) y:= by
  apply (A.glorious x hu t).climb _ le_rfl
  unfold fare capita; rw [show toll G n t k d 1*momentPrice k a * _= A.sizeC*(toll G n t k d 1*(momentPrice k a*Real.exp (a*A.momentum))) from (by ring)]; exact mul_le_mul_of_nonneg_left ((late G d hu.pos n t k _).trans (mul_le_mul_of_nonneg_left (spendMoment k ha (Nat.cast_nonneg _)) (toll_core G _ _ _ hu.pos _))) A.nn_size
end smooth
end YM.Qlocal.Quipu.Sonnet.Vase
