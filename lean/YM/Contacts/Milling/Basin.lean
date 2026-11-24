import YM.Contacts.Milling.Mallet
import YM.PertExtension.BareChart
/-! Parameter-window surgery with the actual product Haar. Chart density
already included in action via own jets. Moving tests and aperture measure. -/
noncomputable section
namespace YM.Contacts.Milling
open Function Set Filter Metric MeasureTheory
open Finset Lattice RG Wilson Precision PertExtension.Series PertExtension.GaussianScore Pulse Pulse.Form Radial
open PertExtension.Chart
open scoped Topology BigOperators ContDiff Classical
variable {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
   [MeasurableSpace E][BorelSpace E]{ι I: Type} [Fintype I][Fintype ι]{G:Gauge}
local notation "ξ" => (ℝ × E)
local notation "κ" => (I → G.Color)
local notation "τ" => (I → G.El)
local notation "μ" => tangent G I
local notation "φ" => 𝓝[>] (0:ℝ)
variable {P:ChartRatio G}(Q:LocalRatio P)
-- Law normalized by Chart.jac0 (parameter-free).
structure Faces (P : ChartRatio G)(B:ξ→ τ →ℝ)(F:ξ × κ→ℝ) (A:ℝ): Prop where
  nz : 0<A
  prices x : Measurable (B x)
  chart : ∀ᶠ z : ξ×κ in 𝓝 0, z.1.1>0 → jacobian P z.2 * B z.1 (expLinks G I z.2)=A*Real.exp (-F z/z.1.1^2)
variable {B B':(ℝ × E)→ (I → G.El)→ℝ}{F:(ℝ × E) ×(I→G.Color)→ℝ}{A:ℝ}
def beach (B:ξ→τ→ℝ)(U:Set τ)(t:ℝ)(x:E): ℝ:= (t^ Module.finrank ℝ κ)⁻¹ * ∫ y in U,B (t,t•x) y ∂physical G I
lemma spaces (f:κ→ℝ)(r:Set κ)(t:ℝ)(ht:0≤t)(hr: MeasurableSet r): (t^ Module.finrank ℝ κ)⁻¹ * (∫ y in r,f y ∂μ)= ∫ y in ((fun y:κ=>t•y) ⁻¹' r), f (t•y) ∂μ:= by
  let ℓ:= fun y:κ=> t•y; have he:= Measure.integral_comp_smul_of_nonneg μ (r.indicator f) t (hR:=ht)
  rw [integral_indicator hr,smul_eq_mul] at he; rw [← he]; let H:=ℓ ⁻¹' r; rw [← integral_indicator (hr.preimage (show Continuous ℓ by unfold ℓ; fun_prop).measurable)]; rfl
lemma chamber_ball {r q:ℝ}(h:r≤ q): chamber G I r ⊆ chamber G I q:= fun _ hx i _=> image_mono (ball_subset_ball h) (hx i (Set.mem_univ _)) -- arg
lemma image_ball (r:ℝ)(hr:0<r): expLinks G I '' ball 0 r= chamber G I r:= by
  ext x; constructor
  · rintro ⟨y,hy,rfl⟩ i _; rw [ball_pi _ hr] at hy; exact ⟨y i, (hy i (Set.mem_univ i)), rfl⟩
  intro h; choose z H hz using fun i:I=> (show x i∈ G.lieExp '' ball 0 r from h i (Set.mem_univ _)); exact ⟨z,by rw [ball_pi (0:κ) hr]; exact fun i _=> H i,funext hz⟩
include Q in
lemma pocket {r:ℝ}(hr:0<r)(h:r≤small G P) : chamber G I r∈ 𝓝 1 := (Ratio.chamber_open Q h).mem_nhds (fun i _=>⟨0,mem_ball_self hr,(show G.lieExp 0=(1:τ) i by simp)⟩)
variable {v w r:ℝ}
include Q
lemma locale (h:Faces P B F A)(d:ℝ): ∃ q>0,q≤ small G P ∧ ∀ r∈Ioo 0 q,∀ᶠ t in φ, ∀ x∈closedBall (0:E) d, ∀ U:Set τ, MeasurableSet U → U⊆chamber G I r →
   beach B U t x = A * ash μ 1 F t (disc t r ∩ (fun y:κ=>expLinks G I (t•y)) ⁻¹' U) (1,x):= by
  obtain ⟨q,hq,H⟩:= Metric.mem_nhds_iff.mp h.chart; refine ⟨min q (small G P),lt_min hq (Ratio.small_pos Q),min_le_right ..,fun r hr=>?_⟩
  have hi:= hr.2.trans_le (min_le_left ..); have hv:= hr.2.trans_le (min_le_right ..); have he:= hr.1
  filter_upwards [Tested.eventually_pos,Tested.eventually_top (show 0<q/(1+|d|) by positivity)] with t ht hh x hx U hu hy
  let l (i:κ):=expLinks G I i; let f (y:τ):= B (t,t•x) y; have hf: Measurable f := h.prices _
  let PR : Set κ:= ball 0 r; let S:= disc t r ∩ (fun y:κ=> l (t•y)) ⁻¹' U; let k y:= projection 1 F t ((1,x),y)
  let v : Set τ:=chamber G I r; have hS : MeasurableSet S:= (disc_meas ..).inter (hu.preimage (expLinks_meas.comp (by fun_prop)))
  have hq' : (t,t•x)∈ball (0:ξ) q:= by
    rw [mem_ball_zero_iff,Prod.norm_def,norm_smul_of_nonneg ht.le, Real.norm_of_nonneg ht.le]; have h:= (lt_div_iff₀ (by positivity : 0<1+|d|)).1 hh; rw [max_lt_iff]; constructor <;> nlinarith [mem_closedBall_zero_iff.mp hx,le_abs_self d, abs_nonneg d]
  unfold beach; change _ * _= A * ∫ y in S,k y ∂μ
  rw (occs:=.pos [1]) [show U=U∩v from (Set.inter_eq_self_of_subset_left hy).symm,← Measure.restrict_restrict hu,← integral_indicator hu]; rw [Ratio.chamber_integral Q _ ?_ hv he]; swap; · exact (h.prices _).indicator hu
  rw [spaces _ _ t ht.le (isOpen_ball (x:=(0:κ))).measurableSet,← MeasureTheory.integral_const_mul,← integral_indicator hS]; change (∫ y in disc t r, jacobian P (t•y)*U.indicator (B (t,t•x)) (expLinks G I (t • y)) ∂μ)=_; rw [← integral_indicator (disc_meas ..)]; apply integral_congr_ae (Eventually.of_forall fun y=>?_); by_cases he:y∈disc t r
  · rw [indicator_of_mem he]; by_cases hs: y∈ S
    · rw [indicator_of_mem hs,indicator_of_mem (show expLinks G I (t • y)∈ U from hs.2)]; dsimp only [k]; rw [projection_eq]; simp only [Pi.one_apply,one_mul,show t • (((1:ℝ),x),y)=((t,t • x), t • y) from Prod.ext (Prod.ext (by exact mul_one _) rfl) rfl,smul_eq_mul,mul_one]; exact H (show (((t,t•x),t•y):ξ × κ)∈ball 0 q from (by rw [mem_ball_zero_iff, Prod.norm_def,max_lt_iff]; exact ⟨mem_ball_zero_iff.mp hq',(mem_ball_zero_iff.mp he).trans hi⟩)) ht
    rw [indicator_of_notMem hs,indicator_of_notMem (show l (t•y) ∉ U from fun u=>hs ⟨he,u⟩)];ring
  rw [indicator_of_notMem he, indicator_of_notMem (show y∉S from fun u=> he u.1)]
lemma separates {s:Set τ}(h:s∈𝓝 1): ∃ (r:ℝ),0<r ∧ chamber G I r ⊆ s := by
  have hu:Tendsto (expLinks G I) (𝓝 0) (𝓝 1):= by simpa [expLinks,Pi.one_def] using! (continuous_pi (show ∀ i:I, Continuous (fun x:κ=>G.lieExp (x i)) from fun i=>G.lieExp_cont.comp (continuous_apply _))).tendsto 0
  obtain ⟨r,hr,H⟩:= Metric.mem_nhds_iff.mp (hu h); exact ⟨r,hr,by rw [← image_ball r hr]; exact Set.image_subset_iff.mpr H⟩
-- Upper aperture & lower scopes selected once per window. Reuse for transformed B.
structure Sight (B:ξ→τ→ℝ)(g:ξ→ℝ)(b:ℝ)(n:ℕ) : Prop where
    nz:0<b
    weight d: ∃ Ω:Set τ,Ω∈𝓝 1 ∧ ∀ σ:Set τ,σ∈𝓝 1 → ∃ C:ℝ,0≤C ∧ ∀ᶠ t in φ, ∀ x∈closedBall (0:E) d, ∀ U:Set τ, MeasurableSet U → U⊆Ω → σ⊆U → ‖beach B U t x-b*Real.exp (-sample g (1,x) t)‖ ≤ C*t^(n+1)
variable {n:ℕ}{L:Law (I → G.Color)}{Y:(ℝ × E)→ι→ℝ}{T:ι→Module.Dual ℝ (I → G.Color)}{R:ℕ→ Rack ι}
lemma shelterbelt {m:ξ→κ}{g:ξ→ℝ}(hp:Faces P B F A)(h:Arc L Y T R F g m n {z:ξ| z.1=1})(hF:Stationary F)(he:Measurable F)(hg:Stationary g)(hC:Snug R): Sight B g (A*measureT L μ) n:= by
  have hμ := hp.nz; refine ⟨mul_pos hμ (measure_pos μ L),fun d=>?_⟩; obtain ⟨q,hq,hu,hl⟩:= locale Q hp d; obtain ⟨δ,hδ,H⟩:= relief μ h hF he hg hC (max 1 d)
  let r:= min (q/2) δ; have hr : 0<r:= lt_min (half_pos hq) hδ; have hw:r<q:= lt_of_le_of_lt (min_le_left ..) (half_lt_self hq); have hx:r≤δ:= min_le_right ..
  refine ⟨chamber G I r,pocket Q hr (hw.le.trans hu),fun s hs=>?_⟩; obtain ⟨k,hk,hS⟩:= separates Q hs; obtain ⟨D,hD,hH⟩:= H (min k r) (lt_min hk hr); refine ⟨A*D,by positivity,?_⟩; filter_upwards [hl r ⟨hr,hw⟩, hH] with t hl hH x hx' U hU hf hs
  let S:Set κ:= disc t r ∩ (fun y:κ=>expLinks G I (t•y)) ⁻¹' U
  rw [hl x hx' _ hU hf]; change ‖A*_ - A* _ *Real.exp (- (g (t • ((1:ℝ), x)) /t^2))‖≤_; rw [mul_assoc A (measureT L μ), ← mul_sub, norm_mul,Real.norm_of_nonneg hμ.le,← neg_div] -- neg_div direction
  rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hμ.le; refine (hH (1,x) rfl ?_ S ((disc_meas ..).inter (hU.preimage (by fun_prop))) (fun y hy=>⟨Set.preimage_mono (Metric.ball_subset_ball (min_le_right ..)) hy, ?_⟩) (fun y hy=>Set.preimage_mono (Metric.ball_subset_ball hx) hy.1)).2
  · apply mem_closedBall_zero_iff.mpr; change max ‖(1:ℝ)‖ ‖x‖ ≤ max 1 d; rw [norm_one]; exact max_le_max_left _ (mem_closedBall_zero_iff.mp hx')
  apply hs; apply hS; rw [← image_ball k hk]; exact ⟨t• y,Metric.ball_subset_ball (min_le_left k r) hy, rfl⟩
omit Q in
lemma preimage_slots {V :Type}[TopologicalSpace V][One V]{T:ℝ→V→V}(h:Tendsto (uncurry T) (φ ×ˢ 𝓝 1) (𝓝 1)){s:Set V}(hs:s∈𝓝 1): ∃ U:Set V,U∈𝓝 1 ∧ ∀ᶠ t in φ,U⊆(T t) ⁻¹' s := by
  obtain ⟨p,hp,u,hu,H⟩:= Filter.mem_prod_iff.mp (h hs); exact ⟨u,hu,(show ∀ᶠ t in φ,t∈p from hp).mono fun t ht=> fun x hx=>H (show (t,x)∈ p ×ˢ u from ⟨ht,hx⟩)⟩
-- Transform symmetry along reporting curves, normalization same L forced.
omit Q in
lemma shaded {g:ξ→ℝ}{b:ℝ}(h:Sight B g b n){k:ℝ→ τ≃ₜ τ}(hk:Tendsto (fun x:ℝ×τ=> k x.1 x.2) (φ ×ˢ 𝓝 1) (𝓝 1))(he:Tendsto (fun x:ℝ×τ=> (k x.1).symm x.2) (φ ×ˢ 𝓝 1) (𝓝 1))
    (x y:ℝ→E)(hp:∀ᶠ t in φ, MeasurePreserving (k t) (physical G I) (physical G I) ∧ B (t,t• (y t)) ∘ k t = B (t,t•(x t))) {d:ℝ} (hm:∀ᶠ t in φ, ‖x t‖≤d ∧ ‖y t‖≤d): Tested.Bill (n+1) (fun t=> Real.exp (-sample g (1,x t) t)-Real.exp (-sample g (1,y t) t)) := by
  obtain ⟨Ω,hΩ,H⟩:= h.weight d; obtain ⟨U,hU,He⟩:= preimage_slots (T:=fun t x=>k t x) hk hΩ; let W:= interior (Ω ∩ U); have hW: W ∈𝓝 1:= interior_mem_nhds.mpr (Filter.inter_mem hΩ hU); have hu := isOpen_interior (s:=Ω∩U) |>.measurableSet; obtain ⟨K,hK,Hk⟩:= preimage_slots (T:=fun t x=>(k t).symm x) he hW
  obtain ⟨C,hC,hv⟩:= H (W∩K) (Filter.inter_mem hW hK); have hb:= h.nz; refine ⟨(C+C)/b,by positivity,?_⟩; filter_upwards [hv,He,Hk,hm,hp] with t hv he hl hx H
  let v:= (k t) '' W; have hw : W ⊆ Ω ∩ U := interior_subset;
  have ho : beach B W t (x t)=beach B v t (y t):= by
    unfold beach; rw [← H.2]; congr 1; let u:τ≃ᵐτ:= (k t).toMeasurableEquiv; have ht : MeasurePreserving u (physical G I) (physical G I) := H.1; conv_rhs=> rw [← ht.setIntegral_preimage_emb u.measurableEmbedding]; tactic=> skip
    rw [show u ⁻¹' v=W from Set.preimage_image_eq W u.injective]; rfl
  have hg : MeasurableSet v:= (Homeomorph.isOpenMap (k t) W isOpen_interior).measurableSet; have hσ : K⊆v:= by intro i hi; exact ⟨(k t).symm i, hl hi,(k t).apply_symm_apply i⟩
  have h1:= hv (x t) (mem_closedBall_zero_iff.mpr hx.1) W hu (hw.trans inter_subset_left) inter_subset_left; have h2:= hv (y t) (mem_closedBall_zero_iff.mpr hx.2) v hg (Set.image_subset_iff.mpr ((hw.trans inter_subset_right).trans he)) (inter_subset_right.trans hσ)
  set p:= Real.exp (-sample g (1,x t) t); set q:= Real.exp (-sample g (1,y t) t); apply le_of_mul_le_mul_left (a:=b) ?_ hb
  change b*‖p-q‖ ≤ _; rw [← Real.norm_of_nonneg (r:=b) hb.le, ← norm_mul, mul_sub]; simp only [Real.norm_of_nonneg hb.le]; rw [← ho] at h2; apply (show ‖b*p-b*q‖≤_ from (by simpa only [dist_eq_norm_sub] using dist_triangle (b*p) (beach B W t (x t)) (b*q))).trans
  rw [norm_sub_rev (b*p)]; apply (add_le_add h1 h2).trans_eq; field_simp
end YM.Contacts.Milling
