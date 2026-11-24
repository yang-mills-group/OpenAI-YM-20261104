import YM.Pert.Triangle.Estimate
/-! Uniform high-radius asymptotics of the mixed outer-line integral. Near a stationary finite-radius mark use coordinates centered separately on that mark. This avoids unjustified common pointwise domination with drifting singularities. Distinctness with quantitative clearance required. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Analysis Set Function Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
local notation "I3" => Fin 3

def radial (r : ℝ) (u : E4) := r • u
lemma radialNorm {d:E4} {r:ℝ} (hd : ‖d‖=1) (hr : 0<r) : ‖radial r d‖=r := by rw [radial,norm_smul,Real.norm_of_nonneg hr.le,hd,mul_one]
variable {B : ℝ} {r : ℝ} {x y d : E4}
lemma rangeHole (hd : ‖d‖=1) (hr : 8*B<r) (hx : ‖x‖≤B) (hy:‖y‖≤B) :
    r/4 ≤ pairHole (radial r d) x y ∧ pairHole (radial r d) x y ≤ r*(5/8) := by
  have hz : 0<r := by linarith [norm_nonneg x]
  have h := radialNorm hd hz
  let z := radial r d
  change ‖z‖=r at h
  have e (v:E4) (hv:‖v‖≤B) : r/2 ≤ ‖z-v‖ ∧ ‖z-v‖ ≤ 5*r/4 := ⟨by linarith [norm_sub_norm_le z v],by linarith [norm_sub_le z v]⟩ -- z mismatch
  unfold pairHole
  change r/4 ≤ min ‖z-x‖ ‖z-y‖ / 2 ∧ min ‖z-x‖ ‖z-y‖ /2 ≤ _
  exact ⟨by linarith [le_min (e x hx).1 (e y hy).1],by linarith [min_le_left ‖z-x‖ ‖z-y‖,(e x hx).2]⟩
lemma bulletFar {w:E4} (hd:‖d‖=1) (hr:8*B<r) (hx : ‖x‖≤B) (hy:‖y‖≤B) (h : w∉zone (radial r d) x y) :
    r/4 ≤ ‖radial r d - w‖ := (rangeHole hd hr hx hy).1.trans (le_of_not_ge fun e=>h (mem_closedBall_iff_norm.mpr (Eq.trans_le (norm_sub_rev w (radial r d)) e)))
variable (i t:I3)
def permitted (i t:I3) (r:ℝ) (d x y w : E4):ℝ := if w∈zone (radial r d) x y then 0 else r^4*mixed i t (radial r d-w)
include B in
lemma permitLimit {R:ℕ→ℝ} (hR : Tendsto R atTop atTop) {δ:ℕ→E4} (hδ : Tendsto δ atTop (𝓝 d)) (hD:∀ i, ‖δ i‖=1) {X Y Z:ℕ→E4}
    (hX : ∀ i, ‖X i‖≤B) (hY : ∀ i, ‖Y i‖≤B) {wlim:E4} (hZ : Tendsto Z atTop (𝓝 wlim)):
    Tendsto (fun k=>permitted i t (R k) (δ k) (X k) (Y k) (Z k)) atTop (𝓝 (mixed i t d)) := by
  have hd : ‖d‖=1 := tendsto_nhds_unique hδ.norm (by simp only [hD];exact tendsto_const_nhds)
  have h1 : Tendsto (fun k=>δ k - ((R k)⁻¹ • Z k)) atTop (𝓝 (d-(0:ℝ) • wlim)) := Filter.Tendsto.sub hδ ((tendsto_inv_atTop_zero.comp hR).smul hZ)
  simp only [zero_smul,sub_zero] at h1
  refine (((mixed_rays i t).diff (by intro e; simp [e] at hd)).continuousAt.tendsto.comp h1).congr' ?_
  filter_upwards [hZ.norm.eventually_lt_const (u:=‖wlim‖+1) (by linarith), hR.eventually (eventually_gt_atTop (8*B+4*(‖wlim‖+1)))] with k hZ hR
  have h := hD k
  have hx := hX k
  have hB := norm_nonneg (X k)
  have hy := hY k
  have hr : 8*B<R k := by linarith [norm_nonneg wlim]
  have hr' : 0 < R k := by linarith [norm_nonneg (X k)]
  have f := norm_sub_norm_le (radial (R k) (δ k)) (Z k)
  rw [radialNorm h hr'] at f
  dsimp only [comp_apply]
  rw [permitted,if_neg (show Z k∉zone _ (X k) (Y k) from fun hz=>by
        have hz' := (mem_closedBall_iff_norm.mp hz).trans (rangeHole h hr hx hy).2
        rw [norm_sub_rev] at hz'
        linarith)]
  let u := δ k - ((R k)⁻¹ • Z k)
  have he : (R k) • u = radial (R k) (δ k) - Z k := by rw [smul_sub,smul_inv_smul₀ hr'.ne'];rfl
  rw [←he]
  exact ((mixed_rays i t).stretch (x:=u) (a:=R k) (by intro e; rw [←he,e,smul_zero,norm_zero] at f; linarith) hr'.ne').symm
lemma permitPrice :
    ∃ C>0, ∀ B x y r d, ‖x‖≤B → ‖y‖≤B → ‖d‖=1 → 8*B<r →
    ∀ w, ‖permitted i t r d x y w-mixed i t d‖ ≤ C := by
  obtain ⟨K,hK,ht⟩ := price (mixed_rays i t)
  refine ⟨(4^4*K)+K,by positivity,?_⟩
  intro B x y r d hX hY hd hr w
  have h : 0<r := by linarith [norm_nonneg x]
  have he := ht d (by intro e; simp only [e,norm_zero] at hd; linarith)
  rw [hd,one_pow,div_one] at he
  apply (norm_sub_le ..).trans
  gcongr
  unfold permitted
  split_ifs with hh
  · rw [norm_zero]; positivity
  have e := bulletFar hd hr hX hY hh
  let ρ := ‖radial r d - w‖
  have e' : 0<ρ := by dsimp [ρ]; linarith
  rw [norm_mul, Real.norm_of_nonneg (by positivity)]
  grw [ht _ (norm_pos_iff.mp e')]
  rw [mul_div_assoc',div_le_iff₀ (show 0<ρ^4 by positivity)]
  calc r^4*K ≤ (4*ρ)^4*K := mul_le_mul_of_nonneg_right (by gcongr; linarith) hK.le
       _ = 4^4*K*ρ^4 := by ring

def capper (B C : ℝ) (w : E4) :=
  if w ∈ closedBall 0 (2*B) then 8*C/‖w‖^3 else (2^9*C)/(1+‖w‖)^6
lemma capperNonnegative (B:ℝ) {C :ℝ} (h:0<C) (w:E4) : 0 ≤ capper B C w := by unfold capper; split_ifs <;> positivity
lemma capper_pay (hB : 0≤B) {C:ℝ} (h : 0<C) : Integrable (capper B C) := by
  let f(w:E4) := 8*C/‖w‖^3
  let S := closedBall (0:E4) (2*B)
  have hS:= isClosed_closedBall (x:=(0:E4)) (ε:=2*B) |>.measurableSet
  have hm : Measurable f := measurable_const.div (measurable_id.norm.pow_const _)
  have hloc := locallyIntegrable_of_norm_le_rpow (μ:=volume) (f:=f) (α:=(3:ℕ)) (C:=8*C) (by norm_num [four_rank]) (by norm_num [four_rank]) (Eventually.of_forall fun _=>by rw [Real.norm_of_nonneg,inv_power];rfl; dsimp [f]; positivity) hm.aestronglyMeasurable
  rw [show capper B C = S.piecewise f (fun w=>(2^9*C)/(1+‖w‖)^6) by funext; rfl]
  exact Integrable.piecewise hS (hloc.integrableOn_isCompact (isCompact_closedBall ..)) (pay_outer _).integrableOn
lemma continues (v:E4) (w : E4) (hB:8≤B) (hv:‖v‖≤B/2) (hw:w ∉ closedBall (0:E4) (2*B)) :
   (1+‖w‖)/2 ≤ ‖w+v‖ := by
  have h := norm_sub_norm_le w (-v)
  rw [sub_neg_eq_add,norm_neg] at h
  have e : 2*B < ‖w‖ := lt_of_not_ge (by simpa only [mem_closedBall_iff_norm,sub_zero] using hw)
  linarith
end YM.Pert.Triangle
