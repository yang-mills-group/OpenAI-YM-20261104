import YM.SchemeConversionRG11.FirstW.Ship.Pleat
/-! Geometry near and far from the image such that ANY engineering power of spacing OK. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Set Metric Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical
variable {T : Itinerary} {G : Gauge}
def remote (x y : StepPath T) : Prop:= ∀ᶠ i:ℕ in atTop, (↑(T.period i).val:ℝ) ≤ 4*cy (x i-y i)
lemma remote_from (h : ∀ i,4∣(T.period i).val) (x y : StepPath T) {u v:E4} (hx : Home T x u) (hy : Home T y v) : remote x (-y) := by
  let q : ℕ→Cover:=fun i=>rel T x i+rel T y i+0
  have he : Tendsto (fun i=>Full.incVec (T.gap i) (q i)) atTop (𝓝 (u+v)) := by unfold q; simp only [add_zero,inc_add]; exact Tendsto.add hx hy
  refine (simple_bounds T he).mono fun i hi=>?_
  have H : x i-(-y) i= Full.center _+Full.center _+wrap _ (q i) := by dsimp only [q,Pi.neg_apply]; rw [add_zero, map_add]; nth_rw 1 [position_rel T x i, position_rel T y i]; abel
  have hj:=dist_half (h i) _ 0 (hi 0) H; rw [Int.abs_eq_natAbs] at hj; have hf : ((T.period i).val) ≤ 4*pdist (x i-(-y) i) := Nat.le_trans (show _ ≤ 4*(lift _ (0:Axis)).natAbs by exact_mod_cast hj) (Nat.mul_le_mul_left 4 (component_le ..)); rw [cy_eq]; have ht : (↑(T.period i).val:ℝ) ≤ 4*(↑(pdist (x i-(-y) i)):ℝ) := by exact_mod_cast hf
  linarith
lemma remote_com (x y : StepPath T) (h : remote x y) : remote y x := h.mono fun i hi=> by rw [show y i-x i= -(x i-y i) by abel,cy_neg]; exact hi
lemma spl_tip (A : Sight T G) (x y : StepPath T) (hp : Splines T x A) (hr : remote y x) : Tip T y A := by
  intro v b
  obtain ⟨H,hP,e⟩:=hp v b; apply Fleck.seale (C:=4*H)
  filter_upwards [e,hr] with i he h
  let s := y i-x i; have hh : cy s *lag s≤1 := by
    unfold lag; rw [←div_eq_mul_inv,div_le_one (pow_pos (zero_lt_one.trans_le (unit_cy _)) _)]
    exact le_self_pow₀ (unit_cy _) (by decide)
  change _*‖A i (y i+wrap (T.period i) v,b)‖≤_
  exact le_trans (mul_le_mul h (he (y i)) (norm_nonneg _) (show 0≤4*cy s by linarith [unit_cy s])) (by change (4*cy s)*(H * lag s)≤_; rw [show 4*cy s*(H*lag s)=4*H*(cy s*lag s) by ring]; nlinarith)
lemma spline_cost (A : Sight T G) (x y : StepPath T) (hA : Splines T x A) : Gentle T y A := by
  intro v b
  obtain ⟨H,hP,hW⟩ := hA v b; apply Dear.tower (C:=H)
  exact hW.mono fun i hi=> (hi (y i)).trans (mul_le_of_le_one_right hP.le (lag_light _)) -- H shadow
lemma river_cost (v : Labels.Key G) (x y : StepPath T) : Gentle T y (fun i=>river (T.gap i) v (x i)) := fun z b=> Dear.sale (spline_cost _ x y (canal_base T v x) z b) _
lemma river_tip (v : Labels.Key G) (x y : StepPath T) (h : remote y (-x)) : Tip T y (fun i=> reflectT G (T.period i) (river (T.gap i) v (x i))) := by
  intro z b; simp only [river,map_smul,Pi.smul_apply]
  exact Fleck.sale (spl_tip _ (-x) y (spline_image (canal_base T v x)) h z b) _
lemma tally (A B C : Sight T G) (x y z : StepPath T) (hA : Splines T x A) (hB : Splines T y B) (hC : Splines T z C) (hr : remote x y) (w : Walk) : Fleck T (fun i=> ∑ v : Site (T.period i),tower G v w (A i) (B i) (C i)) := by
  obtain ⟨D,hD,H⟩:=lagoon_tri x y z hA hB hC w; apply Fleck.seale (C:=4*D*(4*billCap))
  filter_upwards [H,hr] with i hi h
  refine le_trans (mul_le_mul h ((norm_sum_le ..).trans (Finset.sum_le_sum fun a _=>hi a)) (norm_nonneg _) (by have hv := unit_cy (x i-y i); positivity)) ?_
  rw [← Finset.mul_sum]; linarith only [mul_le_mul_of_nonneg_left (night_tri (x i) (y i) (z i)) (show 0≤D from hD.le)]
lemma tuck (A B C : Sight T G) (x y z : StepPath T) (hA : Splines T x A) (hB : Splines T y B) (hC : Splines T z C) (hr : remote x y) : Fleck T (fun i=> wheels (fun v w=>tower G v w (A i) (B i) (C i))) := by
  unfold wheels; have ht(i:ℕ) : ∑ v,∑ u:Ticket,∑ s:Ticket,tower G v (icon (fresh u) (fresh s)) (A i) (B i) (C i) = ∑ u:Ticket,∑ s:Ticket, ∑ v,tower G v (icon (fresh u) (fresh s)) (A i) (B i) (C i) := by rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun v _=> Finset.sum_comm
  simp_rw [ht]; exact Fleck.collect (fun u _ => Fleck.collect (fun b _=> tally A B C x y z hA hB hC hr (icon (fresh u) (fresh b))))
end YM.RG11.FirstW
