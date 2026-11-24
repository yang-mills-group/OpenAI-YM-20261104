import YM.SchemeRG11.Steam.Tip
/-!
The heat equation on a d4 tripod apex. Pointwise positive times; at the face the
other two letters are already anchored at distinct marks.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster MSbar
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
local notation "Tri" => Nodes 4

-- Crude uniform bounds on the time differentiation at a fixed positive time
private lemma stamina (x : E4) {U : ℝ} (hu : 0<U) : ∃ C>0, ∀ u≥U, ∀ a : Axis, ∀ w:E4,
    ‖tint [a,a] u (x-w)‖ ≤ C*(1+‖w‖)^2 := by
  have he {u} (h : U≤u) (z:E4): ‖gauze u z‖ ≤ base*(U^2)⁻¹ := by
    have ht:=hu.trans_le h; have hz : 0<α u:=by unfold α; positivity
    have hB : 0<base:=by unfold base; positivity
    unfold gauze; rw [Real.norm_of_nonneg (by positivity : 0 ≤ base*(u^2)⁻¹*Real.exp (-α u*‖z‖^2))]
    grw [Real.exp_le_one_iff.mpr (by rw [neg_mul]; exact neg_nonpos.mpr (by positivity) : -α u*‖z‖^2 ≤ 0),←h]
    rw [mul_one]
  let c := α U
  have hc : 0<c:=by unfold c α; positivity
  let d:= base*(U^2)⁻¹; have hd : 0<d:=by unfold d base; positivity
  refine ⟨(2*c+(2*c)^2*(1+‖x‖)^2)*d,by positivity,fun u h a w => ?_⟩
  rw [second_line]; dsimp only; rw [norm_mul]; refine (mul_le_mul (norm_add_le ..) (he h _) (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).trans ?_
  rw [show basis a a=(1:ℝ) by simp,mul_one,norm_mul ((2*α u)^2) _]
  have ht:=hu.trans_le h
  have hz:0<α u:=by unfold α; positivity
  have hv: α u≤c:= by unfold c α; gcongr
  have hk : ‖(x-w) a‖≤(1+‖x‖)*(1+‖w‖):= by
    rw [Real.norm_eq_abs,← basis_inner];grw [abs_real_inner_le_norm]; simp only [basis_norm,one_mul]; apply (norm_sub_le ..).trans; nlinarith [norm_nonneg x,norm_nonneg w]
  change (_+_)*d≤_; rw [show ‖-2*α u‖=2*α u by rw [neg_mul,norm_neg,Real.norm_of_nonneg (by positivity)], Real.norm_of_nonneg (sq_nonneg _), norm_mul]
  calc _ ≤ (2*c+ (2*c)^2 * (((1+‖x‖)*(1+‖w‖))*((1+‖x‖)*(1+‖w‖))))*d := by gcongr
       _ ≤ _ := by nlinarith [norm_nonneg w,show 0≤ c*d by positivity, show 0≤‖w‖*(c*d) by positivity,show 0≤‖w‖*(c*d)*‖w‖ by positivity]

variable (V W : Sl) (x : Tri) {q r : ℝ} (hq : 0<q) (hr : 0<r)
def Surf (t q r : ℝ) := ∑ a:Axis, orb [a,a] V W (t,q,r) x
include hq hr
lemma glory {t:ℝ} (ht : 0<t) : HasDerivAt (fun t=> orb [] V W (t,q,r) x) (Surf V W x t q r) t := by
  let T:= Ioi (t/2)
  have hh : 0<t/2:=half_pos ht
  have hc : t∈T:=half_lt_self ht
  have hw (u) (hu:u∈T): (u,q,r)∈tripod:= ⟨lt_trans hh hu,hq,hr⟩
  let F := fun u w=>juice [] V W (u,q,r) x w
  let G := fun u w=> ∑ a:Axis, juice [a,a] V W (u,q,r) x w
  obtain ⟨C,hC,c⟩:=stamina (x 0) hh
  obtain ⟨A,hA,a⟩:=sheer V hq 7 ‖x 1‖
  obtain ⟨B,hB,b⟩:=sheer W hr 0 ‖x 2‖
  let Z:=fun w:E4=> C*A*B/(1+‖w‖)^5
  have hZ (u) (hu : u∈T) (i : Axis) (w:E4) : ‖juice [i,i] V W (u,q,r) x w‖ ≤ Z w := by
    unfold juice; dsimp only; simp only [norm_mul]
    grw [c u (le_of_lt hu) i w,a _ w le_rfl,b _ w le_rfl]; unfold Z; field_simp
    linarith
  have hp: Integrable Z volume:= by
    have he:= integrable_one_add_norm (μ:=volume (α:=E4)) (by norm_num [Axis] : (Module.finrank ℝ E4:ℝ)<5)
    convert! he.const_mul (C*A*B) using 1; ext z; dsimp only [Z]; rw [Real.rpow_neg (by positivity),Real.rpow_ofNat, div_eq_mul_inv]
  have hG u (hu : u∈T): Integrable (G u) volume:= integrable_finsetSum _ (fun i _=> juice_cost _ _ _ _ (hw u hu) x)
  have hs:= (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (F':=G) (bound:=fun w=>∑ _ : Axis,Z w) (isOpen_Ioi.mem_nhds hc) (Eventually.mono (isOpen_Ioi.mem_nhds hc) (fun u hu=> (juice_cost [] V W _ (hw u hu) _).aestronglyMeasurable)) (juice_cost [] V W _ (hw t hc) _) (hG _ hc).aestronglyMeasurable (Eventually.of_forall fun w u hu=> (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> hZ u hu i w))) (integrable_finsetSum _ (fun i _=>hp)) (Eventually.of_forall fun w u hu=> by
       unfold F G juice; dsimp only; rw [←Finset.sum_mul,←Finset.sum_mul]; exact (((stave (x 0-w) (hh.trans hu)).mul_const _).mul_const _))).2
  convert! (hs.congr_of_eventuallyEq (f₁:=fun t=>orb [] V W (t,q,r) x) (Eventually.mono (isOpen_Ioi.mem_nhds hc) fun u hu=> grape _ _ _ _ (hw u hu) x)) using 1
  unfold G; rw [integral_finsetSum _ (fun i _=> juice_cost _ _ _ _ (hw t hc) x)]
  unfold Surf; simp only [grape _ _ _ _ (hw t hc)]

variable (hx : x∈ clearance 4)
include hx
lemma thinning : Tendsto (fun t=> orb [] V W (t,q,r) x) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩:= Cluster.respite zero_lt_one isCompact_singleton (singleton_subset_iff.mpr hx) ((sumBits [] V W).map atEye)
  have hh (t:ℝ) (ht:0<t) : ‖orb [] V W (t,q,r) x‖ ≤ C/wages (t,q,r) := by
    rw [← Complex.norm_real,show ((orb [] V W (t,q,r) x:ℝ):ℂ)=_ from congr_fun (spin_four 1 ((sumBits [] V W).map atEye) (t,q,r)).symm x]
    exact h (t,q,r) ⟨ht,hq,hr⟩ _ rfl
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun t : ℝ=>norm_nonneg _) ((eventually_gt_atTop _).mono fun t ht=>hh t ht) ?_)
  have hu:Tendsto due atTop atTop := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<4/3)).comp (show Tendsto (fun t:ℝ=>1+t) atTop atTop from tendsto_atTop_add_const_left _ _ tendsto_id)
  have hb:Tendsto (fun t=> wages (t,q,r)) atTop atTop:= (tendsto_mul_const_atTop_of_pos (dues hr)).mpr ((tendsto_mul_const_atTop_of_pos (dues hq)).mpr hu)
  simpa only [div_eq_mul_inv,comp_def,mul_zero] using (tendsto_inv_atTop_zero.comp hb).const_mul C
end YM.SchemeRG11.Steam
