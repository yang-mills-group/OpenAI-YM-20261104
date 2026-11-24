import YM.RG01.Sounder.Infinite
import YM.Work.F05.Actions
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brush
/-! # Price *actual unmasked* stencil families and symbol images on all
positions, including the entire station travel (uses split-exp
real receipts). Inputs at grade n+k etc, require genuine summability
of the atom/path coefficients through that grade with EXPONENTIAL widths;
may independently be produced on each auxiliary admissible mesh.
No causal comparison or assumption identifying phases, or assumption of model
supremum or of actual remainder. Credits here on unmarked translating shells. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Sounder
open AnalyticNext.QuarticMatch.Estimate Push.Uniform Gauge Logfee
open Lattice Wilson RG RG.Supply Input Precision Tree Pressure
open ConnectedActivityE6 Blaze Brush
open Work.F05 Work.F02 Filter Function MeasureTheory ProbabilityTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
open NormedSpace Finset Metric
variable {G:Gauge}{k n j :ℕ}{l:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
-- signed mask independent. unmasked ALL, no failed contribution lemma here.
/-- A SELF PAID sequence of physical paths of rank k with honest exponential envelope. -/
structure book (G:Gauge)(k:ℕ) where
  words : ℕ → RG.Atom G k
  width : ℝ
  owes : ℝ
  pos : 0<width
  fee : SumBudget (fun n=> (words n).budget width) owes
  inv : ∀n,(words n).Invariant
namespace book
variable (W:book G k)
def slab (s:Signed) (x:Site l) (U:Config G l):ℝ:= ∑' n,(W.words n).unmasked (pull s 0 U) x
lemma slab_fee (s:Signed) (x:Site l) (U:Config G l) (n:ℕ): ‖(W.words n).unmasked (pull s 0 U) x‖ ≤ (W.words n).budget W.width* (2:ℝ)^k :=
  ((W.words n).unmasked_bound _ _).trans (mul_le_mul_of_nonneg_right ((W.words n).lower_budget W.width W.pos) (by positivity))
lemma slab_bound (s:Signed)(x:Site l)(U:Config G l):‖W.slab s x U‖ ≤ W.owes * (2:ℝ)^k:=by
  unfold slab; have hs:=W.fee.2.1.mul_right ((2:ℝ)^k)
  have ht:= Summable.of_nonneg_of_le (fun n=>norm_nonneg _) (W.slab_fee s x U) hs
  apply (norm_tsum_le_tsum_norm ht).trans ((Summable.tsum_le_tsum (W.slab_fee s x U) ht hs).trans ?_)
  rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right W.fee.2.2 (by positivity)
lemma slab_meas (s:Signed)(x:Site l):Measurable (W.slab s x):=by
  apply Measurable.tsum; intro i; apply Continuous.measurable; fun_prop
lemma slab_gi (s:Signed)(x:Site l):GaugeInvariant (W.slab s x):=by
  intro t U; unfold slab; apply tsum_congr; intro i; simp only [pull_gauge_zero,RG.Atom.unmasked, slot_gauge]; apply W.inv i
/-- For exposing economically root-held assumptions with signed translation
 price per orientation AND site; s can be fixed, β convention from producer. -/
def settle (s:Signed)(U:Config G l):= ∑ x : Site l,W.slab s x U
def toll (w:ℕ):ℝ:=w*(W.owes*2^k)
lemma settle_est (s:Signed)(U:Config G l): ‖W.settle s U‖ ≤ W.toll (Fintype.card (Site l)):=by
  unfold settle toll; apply (norm_sum_le ..).trans ((sum_le_sum fun i _=>W.slab_bound s i U).trans_eq ?_); rw [sum_const,card_univ,nsmul_eq_mul]
lemma paid:(0:ℝ) ≤ W.owes:= (W.fee.1 0).trans ((Summable.le_tsum W.fee.2.1 0 (fun i _=> W.fee.1 i)).trans W.fee.2.2)

-- derivative enclosure for ANY torus if per-link Allows all z and translations.
def premium (Y:ℝ)(j:ℕ):ℝ:= composeCost j ((1+(2:ℝ)^j / Work.F02.radius W.width)^j) Y*|Work.F02.slotConst G|^k
lemma summand (U:E→Config G l)(u:E){Y:ℝ} (hy:∀ i:Bond l, Allows j (fun z=>G.mat (U z i)) u Y) (s:Signed)(x:Site l)(n:ℕ):
    Allows j (fun z:E=> (W.words n).unmasked (pull s 0 (U z)) x) u ((W.words n).budget W.width* W.premium Y j):=by
  let q:= W.words n; let X z:= pull s 0 (U z)
  have hY: 0≤Y:= (hy (Classical.arbitrary _)).nonneg
  have hh (i: Bond l): Allows j (fun z=>G.mat (X z i)) u Y:=by
    let d:= (posDir i.2).rotate s; let y:= affine s (0:Site l) i.1
    have h:= hy (d.used y)
    unfold X pull Lattice.Step.read; split
    · exact h.inverse (f:=fun z=>U z _)
    exact h
  have hb: 0≤ q.budget W.width:= W.fee.1 n
  let M:= q.budget W.width*|Work.F02.slotConst G|^k
  have hg : (fun z=> physical (X z)) u= physical (X u):=rfl
  have hf := allows_real_of_entire j (atomExt_contDiff q x) (Work.F02.radius_pos W.pos) (fun y hy=> (atomExt_bound q (X u) W.pos y (ball_subset_closedBall hy) x).trans (show _≤ M by unfold M; exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans_eq (abs_pow _ _)) hb ))
  have he (z): Complex.reCLM (atomExt q x (physical (X z))) = q.unmasked (X z) x := by rw [Work.F02.atomExt_physical]; rfl
  have hX:= (hf.comp (f:=fun z=>physical (X z)) (allows_ambient hh)).linear Complex.reCLM Complex.reCLM_norm.le
  simp_rw [he,one_mul] at hX
  apply hX.mono
  unfold M premium q composeCost; ring_nf; exact le_rfl

lemma slab_notes (U:E→Config G l){Y:ℝ}(hy:∀(z:E)(i:Bond l), Allows j (fun z=>G.mat (U z i)) z Y)(s:Signed)(x:Site l)(u:E):
    Brush j (W.owes*W.premium Y j) 1 (fun z:E=> W.slab s x (U z)) u:=by
  have hY:0≤Y:=(hy u (Classical.arbitrary _)).nonneg
  have hp:0≤W.premium Y j:=by unfold premium composeCost; have h:=radius_pos W.pos; positivity
  let f n (z:E):=(W.words n).unmasked (pull s 0 (U z)) x
  let P (_ n:ℕ):=(W.words n).budget W.width* W.premium Y j
  have h n v:= W.summand U v (hy v) s x n
  have hf n : ContDiff ℝ (j:WithTop ℕ∞) (f n):= contDiff_iff_contDiffAt.mpr (fun i=> (h n i).analytic.of_le le_top)
  have hm (i : ℕ) (_ : (i:ℕ∞)≤ (j:ℕ)):Summable (P i) := W.fee.2.1.mul_right _
  have hc (i n : ℕ) x (hJ : (i:ℕ∞) ≤ (j:ℕ)):‖iteratedFDeriv ℝ i (f n) x‖ ≤ P i n:= (h n x).norm_le i (by exact_mod_cast hJ)
  apply Brush.offer.mpr; constructor
  · exact (contDiff_tsum hf hm hc).contDiffAt
  intro i hi
  have he : (i:ℕ∞) ≤ (j:ℕ∞):= Nat.cast_le.mpr hi
  change ‖iteratedFDeriv ℝ i (fun x:E=>∑' n,f n x) u‖ ≤ _
  rw [iteratedFDeriv_tsum_apply hf hm hc he]
  let T n:=iteratedFDeriv ℝ i (f n) u
  have hs:Summable (fun n=> ‖T n‖):=Summable.of_nonneg_of_le (fun n=>norm_nonneg _) (fun n=>hc i n u he) (hm i he)
  apply (norm_tsum_le_tsum_norm hs).trans ((Summable.tsum_le_tsum (fun n=>hc i n u he) hs (hm i he)).trans ?_)
  unfold P; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right W.fee.2.2 hp
lemma settle_notes (U:E→Config G l){Y:ℝ}(hy:∀(z:E)(i:Bond l), Allows j (fun z=>G.mat (U z i)) z Y)(s:Signed)(u:E):
    Brush j ((Fintype.card (Site l):ℝ)*(W.owes*W.premium Y j)) 1 (fun z:E=> W.settle s (U z)) u:=by
  simpa only [sum_const,nsmul_eq_mul,card_univ,settle] using (Brush.spree (Finset.univ:Finset (Site l)) _ _ zero_le_one fun i _=>W.slab_notes U hy s i u)
end book
end YM.RG01.Sounder
