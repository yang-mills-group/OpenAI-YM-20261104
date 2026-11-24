import YM.Next.FOUNDATIONS.Primary
import YM.Next.MULTISOURCE.Wage
import YM.Shoot.Criteria
import YM.SectorNext.VACUUM_NORMALIZATION.Laplace
import YM.UVExt.WilsonAnalytic

/-! Complex inverse-coupling window for the **one-link normalizer only**. Not zero-freeness of the finite Wilson partition function on a volume independent disk. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt
open RG Precision SectorNext.Vacuum Filter Wilson Set MeasureTheory
open scoped Classical ContDiff Topology BigOperators
variable {G : Gauge} (κ : ℝ) (z : ℂ)

def blinkWeight (κ : ℝ) (z : ℂ) (u : G.El) := Complex.exp (-(κ*(G.price u):ℝ)* z)
def complexLinkZ (G : Gauge) (κ : ℝ) (z : ℂ) := ∫ u, blinkWeight (G:=G) κ z u ∂G.probHaar

private lemma blink_real (β : ℝ) (x : G.El) : blinkWeight (G:=G) κ (β:ℂ) x = (mouth G (κ*β) x : ℂ) := by unfold blinkWeight mouth; rw [Complex.ofReal_exp]; congr 1; push_cast; ring -- push cast of ofReal_neg
lemma complexLinkZ_real (β : ℝ) : complexLinkZ G κ (β:ℂ) = (linkZ G (κ*β) : ℂ) := by unfold complexLinkZ linkZ; simp only [blink_real]; exact integral_ofReal
private lemma lapse_real (w v : ℂ) : (-w*v).re = -(w.re*v.re)+w.im*v.im := by simp [Complex.mul_re]; ring
lemma blink_cost (x : G.El) : ‖blinkWeight κ z x‖ = mouth G (κ*z.re) x := by unfold blinkWeight mouth; rw [Complex.norm_exp]; congr 1;  rw [Complex.mul_re, Complex.neg_im, Complex.neg_re, Complex.ofReal_im]; simp only [Complex.ofReal_re,neg_zero]; change - (κ * G.price x) * z.re - 0 * z.im = -(κ*z.re)*G.price x; ring -- parser types
variable (A : ChartRatio G) (h : LocalRatio A)
include h in
lemma link_ratio_bound (hκ : 0<κ) : ∃ C:ℝ,0<C ∧ ∀ᶠ η:ℝ in atTop, linkZ G (κ*(η^2)/4) ≤ C * linkZ G (κ*η^2) := by
  have hl:= first_asymptotic A h κ hκ
  have hu:= first_asymptotic A h (κ/4) (by positivity)
  let c:= narrow A (κ/4)+1; let d:=narrow A κ; let D:=c*2/d
  have hc:0<c:=show 0<narrow A (κ/4)+1 from add_pos (narrow_pos A h _ (by positivity)) zero_lt_one; have hd:0<d:=narrow_pos A h _ hκ; have hD : 0<D := by unfold D; positivity
  refine ⟨D,hD, ?_⟩
  -- cofinal
  filter_upwards [hu.eventually (gt_mem_nhds (a:=c) (by change narrow A (κ/4)<c; dsimp [c];linarith)),hl.eventually (lt_mem_nhds (a:=d/2) (by change d/2<d;linarith)),eventually_gt_atTop (0:ℝ)] with η hcu hcb hη
  rw [show κ*η^2/4=(κ/4)*(η^2) by ring]
  apply le_of_mul_le_mul_left (a:=η^(Module.finrank ℝ G.Color)) _ (pow_pos hη _)
  calc
    _ ≤ c := le_of_lt hcu
    _ = D*(d/2) := by simp [D]; field_simp [hd.ne']
    _ ≤ _ := by rw [mul_left_comm (η^(Module.finrank ℝ G.Color)) D _]; exact mul_le_mul_of_nonneg_left (show d/2 ≤ _ from le_of_lt hcb) hD.le

lemma blink_cont : Continuous (blinkWeight (G:=G) κ z) := by unfold blinkWeight; fun_prop
variable {κ}
private def blinkSlope (κ : ℝ) (s : ℂ) (x : G.El) := blinkWeight κ s x * -((κ*G.price x:ℝ):ℂ)
lemma blink_deriv (x : G.El) : HasDerivAt (fun s:ℂ=>blinkWeight κ s x) (blinkSlope κ z x) z := by
  have h := ((hasDerivAt_id' z).const_mul (-(κ*G.price x:ℝ):ℂ)).cexp
  simpa only [blinkSlope,blinkWeight,mul_one,Complex.ofReal_neg] using h
lemma blink_deriv_size {κ β : ℝ} (hκ : 0 < κ) {x : G.El} {z : ℂ} (hβ:0<β) (hz : β ≤ 2*z.re) : ‖blinkSlope κ z x‖ ≤ 4/β * mouth G (κ*β/4) x := by
  have hn := (G.price_range x).1
  rw [blinkSlope,norm_mul,norm_neg,blink_cost, Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hκ.le hn)]
  have he := Real.add_one_le_exp (κ*β/4*G.price x)
  have hw : mouth G (κ*z.re) x ≤ (Real.exp (-(κ*β/4)*G.price x)) * mouth G (κ*β/4) x := by unfold mouth; rw [←Real.exp_add]; exact Real.exp_monotone (by nlinarith [mul_nonneg (mul_nonneg hκ.le hn) (show 0≤2*z.re-β from sub_nonneg.mpr hz)])
  calc
    _ ≤ (mouth G (κ*β/4) x * Real.exp (-(κ*β/4)*G.price x)) * (κ*G.price x) := mul_le_mul_of_nonneg_right (by exact hw.trans_eq (mul_comm ..) : mouth G (κ*z.re) x ≤ _) (mul_nonneg hκ.le hn)
    _ = mouth G (κ*β/4) x * ((κ*G.price x)/Real.exp ((κ*β/4)*G.price x)) := by rw [neg_mul,Real.exp_neg]; ring
    _ ≤ _ := by rw [mul_comm (4/β) _]; exact mul_le_mul_of_nonneg_left ((div_le_iff₀ (Real.exp_pos _)).mpr (by rw [div_mul_eq_mul_div,le_div_iff₀ hβ]; linarith)) (mouth_pos ..).le

omit h in
lemma blink_weight_near {β : ℝ} (hκ :0<κ) (hβ: 0<β) (hz : β ≤ 2*z.re) (x : G.El) : ‖blinkWeight κ z x-blinkWeight κ (β:ℂ) x‖ ≤ ‖z-(β:ℂ)‖ * (4/β * mouth G (κ*β/4) x) := by
  let f := fun z:ℂ=> blinkWeight κ z x
  let s := {z':ℂ | β ≤ 2*z'.re}
  change ‖f z-f β‖ ≤ _; rw [mul_comm (‖z-(β:ℂ)‖)]
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜:=ℂ) (s:=s) (fun y hy=> (blink_deriv y x).hasDerivWithinAt) _ _ (show (β:ℂ)∈s by dsimp [s]; linarith) hz
  · intro y hy; exact blink_deriv_size hκ hβ hy
  intro y h₁ x h₂ a b h₀a h0b he
  dsimp [s] at *; change β≤_ at *; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; nlinarith only [mul_nonneg h0b (sub_nonneg.mpr h₂),mul_nonneg h₀a (sub_nonneg.mpr h₁),congr_arg (·*β) he]

lemma bounded_by_linkZ : ‖complexLinkZ G κ z‖ ≤ linkZ G (κ*z.re) := by
  unfold complexLinkZ linkZ; simp_rw [← blink_cost κ z]; exact norm_integral_le_integral_norm _
lemma step_bond {b c : Lattice.Side} (K : StepData b c) (β : ℝ) : complexLinkZ G K.kernel.penalty β = (K.penaltyZ β G:ℂ) := by
  rw [complexLinkZ_real]; unfold linkZ StepData.penaltyZ; simp only [mouth,StepData.penaltyWeight]; congr 1; apply integral_congr_ae; filter_upwards [] with x; congr 1; ring
include h in
lemma near_bond (hκ:0<κ) : ∃ c,0<c∧∀ᶠ β:ℝ in atTop, 0<β ∧ ∀ z∈Metric.closedBall (β:ℂ) (c*β), ‖complexLinkZ G κ z-(complexLinkZ G κ β)‖ ≤ (1/2) * linkZ G (κ*β) := by
 obtain ⟨C,hC,H⟩:=link_ratio_bound κ A h hκ
 let c := min (1/2) (1/(8*C)); have hc := lt_min one_half_pos (show (0:ℝ)<1/(8*C) by positivity)
 refine ⟨c,hc,?_⟩
 filter_upwards [Real.tendsto_sqrt_atTop.eventually H, eventually_gt_atTop (0:ℝ)] with β hβ hP
 simp_rw [Real.sq_sqrt hP.le] at hβ
 refine ⟨hP,fun z hz=> ?_⟩
 change dist z (β:ℂ) ≤ _ at hz; rw [dist_eq_norm] at hz
 have hp := le_trans hz ((le_min_iff.mpr ⟨by nlinarith [min_le_left (1/2:ℝ) (1/(8*C))],by unfold c at *; exact mul_le_mul_of_nonneg_right (min_le_right ..) hP.le⟩) : c*β≤min (β/2) ((1/(8*C))*β))
 have hd : β ≤ 2*z.re := by
    have hh := (Complex.abs_re_le_norm (z-(β:ℂ))).trans (hp.trans (min_le_left ..))
    simp only [Complex.sub_re,Complex.ofReal_re] at hh
    have h1 := (abs_le.mp hh).1; linarith
 let u x := blinkWeight (G:=G) κ z x-blinkWeight κ (β:ℂ) x
 let v x := mouth G ((κ*β)/4) x
 have hi z : Integrable (blinkWeight (G:=G) κ z) G.probHaar := (blink_cont ..).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hv : ∀ x, ‖u x‖ ≤ (‖z-β‖*4/β) * v x := fun x=> (blink_weight_near z hκ hP hd x).trans_eq (by dsimp [v]; ring)
 have hh := (norm_integral_le_integral_norm u (μ:=G.probHaar)).trans (integral_mono ((hi z|>.sub (hi (β:ℂ))).norm) ((mouth_int ..).const_mul _) hv)
 unfold u at hh

 rw [integral_sub (hi _) (hi _),integral_const_mul] at hh
 change ‖complexLinkZ G _ z - complexLinkZ G _ β‖ ≤ _* linkZ G (κ*β/4) at hh
 have hN : 0 ≤ ‖z-(β:ℂ)‖*4/β := by positivity
 apply hh.trans ((mul_le_mul_of_nonneg_left hβ hN).trans ?_)
 rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (show _ ≤ 1/2 by
     have hp1 := hp.trans (min_le_right ..)
     have he : 1/(8*C)*(8*C)=1 := div_mul_cancel₀ _ (by positivity)
     change ‖z-↑β‖ * 4 / β * C ≤ (1/2:ℝ)
     rw [div_mul_eq_mul_div,div_le_iff₀ hP]; nlinarith) (integral_nonneg fun x=> (mouth_pos ..).le)

lemma blink_differentiable : Differentiable ℂ (complexLinkZ G κ) := by
  intro z
  let f := blinkWeight (G:=G) κ; let M := ‖κ‖*2; let c := Real.exp ((‖z‖+1)*M)*M
  have hM : 0≤M := by dsimp [M]; positivity
  have hb {w} {sent:G.El} (hw : w∈Metric.ball z 1) : ‖blinkSlope κ w sent‖ ≤ c := by
     have hh := ((G.price_range sent).1); have hx := ((G.price_range sent).2)
     have ht := (norm_sub_norm_le w z).trans (dist_eq_norm w z ▸ (Metric.mem_ball.mp hw).le)
     have h := Complex.abs_re_le_norm w; have hr : ‖κ*G.price sent‖ ≤ M := le_trans (norm_mul_le ..) (mul_le_mul le_rfl (by rwa [Real.norm_of_nonneg hh]) (norm_nonneg _) (norm_nonneg _))
     rw [blinkSlope,norm_mul, blink_cost,norm_neg,Complex.norm_real]
     change _ ≤ _ * M
     refine mul_le_mul ?_ hr (norm_nonneg _) (Real.exp_pos _).le
     refine Real.exp_monotone <| le_trans (le_abs_self (-(κ*w.re)*G.price sent)) ?_
     rw [show -(κ*w.re)*G.price sent=-(κ*G.price sent)*w.re by ring,abs_mul,abs_neg]; rw [Real.norm_eq_abs] at hr
     exact le_trans (mul_le_mul hr (le_trans h (by linarith)) (abs_nonneg _) hM) (mul_comm ..).le
  let μ := G.probHaar
  have hout : Continuous (blinkSlope (G:=G) κ z) := (blink_cont _ _).mul (Continuous.neg (Complex.continuous_ofReal.comp (continuous_const.mul G.continuous_price))) -- G.continuous_price names
  exact ((hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound:=fun _=> c) (F:=f) (μ:=G.probHaar)
    (Metric.ball_mem_nhds z zero_lt_one) (Eventually.of_forall fun w=> ((blink_cont κ w)).aestronglyMeasurable)
    ((blink_cont (G:=G) κ z).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((show Continuous (blinkSlope (G:=G) κ z) from hout).aestronglyMeasurable)
    (Eventually.of_forall fun U z' hz=>hb hz) (integrable_const _)
    (Eventually.of_forall fun U z' _=>blink_deriv z' U)).2).differentiableAt
lemma blink_positive (β : ℝ) : 0<linkZ G (κ*β) := by
  let m g := mouth G (κ*β) g
  change 0< ∫ g, m g ∂G.probHaar
  apply (integral_pos_iff_support_of_nonneg (fun _=>(mouth_pos ..).le) (mouth_int ..)).2; rw [show Function.support m=univ from Set.eq_univ_of_forall fun _=>(mouth_pos ..).ne']; simp
include h in
lemma tower_band_safe (hG : G.Simple) (B : Levels G) (hκ : 0<κ) : ∃ c,0<c∧∀ᶠ m:ℕ in atTop, ∀ β∈ RG.Shoot.band B m, let r := c*β
   AnalyticOnNhd ℂ (fun z=> (complexLinkZ G κ z)⁻¹) (Metric.ball (β:ℂ) r) ∧ ∀ z ∈Metric.ball (β:ℂ) r, (linkZ G (κ*β))/2≤ ‖complexLinkZ G κ z‖ :=by
  obtain ⟨c,hc,hF⟩:= near_bond (κ:=κ) A h hκ
  obtain ⟨b₀,hB₀⟩ := eventually_atTop.mp hF
  refine ⟨c,hc,((YM.Multi.Wage.hat_tend hG B).eventually_ge_atTop (b₀*2)).mono (fun m hm β hβ=>?_ )⟩
  intro r
  have hu := hB₀ β (by have := hβ.1; change _/2≤ _ at this; linarith)
  let f(z:ℂ) := complexLinkZ G κ z
  have ht : f β=(linkZ G (κ*β):ℂ) := complexLinkZ_real ..
  have hp := blink_positive (G:=G) (κ:=κ) β
  have hb1(z:ℂ)(hz:z∈Metric.ball (β:ℂ) r) : linkZ G (κ*β)/2≤ ‖f z‖ := by
     have h1: ‖f β‖-‖f z‖≤(1/2)*linkZ G (κ*β) := (norm_sub_norm_le (f β) (f z)).trans (by rw [norm_sub_rev]; exact hu.2 z (show z∈Metric.closedBall (β:ℂ) r from Metric.ball_subset_closedBall hz))
     rw [ht,Complex.norm_real,Real.norm_of_nonneg hp.le] at h1; linarith
  refine ⟨fun z hz=> (AnalyticAt.inv ((blink_differentiable (G:=G) (κ:=κ)).analyticAt z) (norm_pos_iff.mp ((half_pos hp).trans_le (hb1 _ hz)))),hb1⟩

omit h in
lemma step_band_safe (hG : G.Simple) (B : Levels G) : ∃ c,0<c∧∀ᶠ m:ℕ in atTop,∀ n:ℕ,∀ β∈ RG.Shoot.band B (m+1), let K:=(B.clock.op m n).kernel
    AnalyticOnNhd ℂ (fun z=> (complexLinkZ G K.penalty z)⁻¹) (Metric.ball (β:ℂ) (c*β)) ∧ ∀ z∈Metric.ball (β:ℂ) (c*β),
      (B.clock.op m n).penaltyZ β G / (2:ℝ) ≤ ‖complexLinkZ G K.penalty z‖ := by
  obtain ⟨c,hc,h⟩:= tower_band_safe (κ:=B.clock.kernel.penalty) (Next.Foundations.chart G) (Next.Foundations.chart_ok G) hG B B.clock.kernel.penalty_pos
  refine ⟨c,hc,(Filter.Eventually.mono ((tendsto_add_atTop_nat 1).eventually h) fun m hm n β hb=>?_ )⟩ -- fix name
  obtain ⟨ht,hv⟩:= hm β hb; intro k
  let d:= (B.clock.op m n)
  have he := (step_bond (G:=G) (B.clock.op m n) β).symm.trans (complexLinkZ_real _ β)
  exact ⟨ht,fun z hz=> (by rw [show (B.clock.op m n).penaltyZ β G=linkZ G (B.clock.kernel.penalty*β) from Complex.ofReal_injective he]; exact hv _ hz)⟩
end YM.UVExt
