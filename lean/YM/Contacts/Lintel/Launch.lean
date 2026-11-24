import YM.Contacts.Lintel.Parity
namespace YM.Contacts.Lintel
set_option linter.unusedSectionVars false
open Function Set Finset Filter Metric RG Wilson Lattice Precision Exterior MeasureTheory
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F05
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Radial
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f m: Side}{α:ℕ→Type}{n k:ℕ}
variable {V X Y E:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
   [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {t:E} {a b:E→ ℝ}
namespace Crag
open Wire
open Tested
variable {F:Type}[MeasurableSpace E][BorelSpace E]{I:Type}[Fintype I]{P:ChartRatio G}
local notation "κ" => (I→G.Color)
local notation "τ" => (I→G.El)
variable (h:LocalRatio P) -- declare ahead? beware local notation in variable blocks.Subst
include h
private theorem exp_small {t:ℝ}(ht:0<t)(hx:t ≤ small G P) : Set.InjOn (expLinks G I) (ball 0 t):= by
   rw [ball_pi _ ht]; intro i hi j hj he; have hy:= hx.trans (min_le_left ..); refine funext fun k=> h.inject (ball_subset_ball ?_ (hi k (Set.mem_univ k))) (ball_subset_ball ?_ (hj k (Set.mem_univ k))) (congr_fun he k); all_goals exact hy.trans (half_lt_self h.patch).le
variable {b:ℝ}{c a:κ} -- notation fail
omit h in
private lemma exp_cont (G:Gauge) (I : Type) [Fintype I]: Continuous (expLinks G I):=continuous_pi fun i=> G.lieExp_cont.comp (continuous_apply i)
private lemma interpose {r t:ℝ} {a:κ}(ht:0<t) (he:t≤ small G P)(H : closedBall a r ⊆ ball 0 t) : MeasurableSet (expLinks G I '' ball a r):= by
   let f:= expLinks G I; let s:= ball a r; let u:= closedBall a r; have hx : f '' s=f '' u\ f '' (u\ s):= by
     ext y; constructor
     · rintro ⟨x,hx,rfl⟩; refine ⟨⟨x, ball_subset_closedBall hx, rfl⟩,fun ⟨z,hz,hp⟩=> hz.2 ((exp_small (I:=I) h ht he (H hz.1) (H (ball_subset_closedBall hx)) hp).symm ▸ hx)⟩
     rintro ⟨⟨x,hx,rfl⟩,ht⟩; refine ⟨x,?_,rfl⟩; by_contra hh; exact ht ⟨x,⟨hx,hh⟩,rfl⟩
   change MeasurableSet (f '' s); rw [hx]; exact (((isCompact_closedBall a r).image (exp_cont G I)).measurableSet.diff ((((isCompact_closedBall a r).diff isOpen_ball).image (exp_cont G I)).measurableSet))
lemma ratio_cell {r t:ℝ}(ht:0<t)(he:t<small G P)(a:κ)(H: closedBall a r⊆ ball 0 t)(f:τ→ℝ) (hf:Measurable f) : (∫ x in expLinks G I '' ball a r, f x ∂physical G I)=(∫ x in ball a r, jacobian P x * f (expLinks G I x) ∂ tangent G I):= by
   let s := ball a r; let V:= ball (0:κ) t; let U:= expLinks G I '' s; have hp:= interpose h ht he.le H; have hu:U⊆ chamber G I t:= by rw [← Milling.image_ball t ht]; exact image_mono (ball_subset_closedBall.trans H)
   let M:=physical G I; rw [← MeasureTheory.Measure.restrict_restrict_of_subset hu,← integral_indicator hp,Ratio.chamber_integral h (φ:=U.indicator f) (hf.indicator hp) he ht] -- signature
   rw [← MeasureTheory.Measure.restrict_restrict_of_subset (ball_subset_closedBall.trans H : s⊆V)]; conv_rhs=> rw [← integral_indicator isOpen_ball.measurableSet]
   refine setIntegral_congr_fun (show MeasurableSet V from isOpen_ball.measurableSet) fun x hx=> ?_; by_cases hi:x∈ s; ·  change jacobian P x * indicator U f (expLinks G I x)= (indicator s (fun x=> jacobian P x*f (expLinks G I x))) x; rw [Set.indicator_of_mem hi,Set.indicator_of_mem (show expLinks G I x∈ U from ⟨x,hi,rfl⟩)]
   change jacobian _ _ * U.indicator f _ = s.indicator _ _; rw [indicator_of_notMem hi,indicator_of_notMem]; exact mul_zero _; rintro ⟨w,hw,hz⟩; exact hi ((exp_small h ht he.le (H (ball_subset_closedBall hw)) hx hz) ▸ hw)
variable {ρ:E→ I→ G.Color}{Y:E→ I→G.El}{M S:E ×(I→G.Color)→ℝ}{B:ℝ×E→(I→G.El)→ ℝ}{F:E→ℝ}
private def theme (c:τ):τ≃ₜτ := (Homeomorph.mulRight c)
private lemma tempest (c:τ): MeasurePreserving (theme c) (physical G I) (physical G I):= by
    apply measurePreserving_pi (fun _=>G.probHaar) (fun _=> G.probHaar) (fun i=> measurePreserving_mul_right G.probHaar (c i)) -- ht arg?
private lemma draw_cost (f:τ→ℝ)(c:τ)(U:Set τ): (∫ x in (theme c) '' U,f x ∂physical G I)=∫ x in U,f (theme c x) ∂physical G I:= by
   let V:= (theme c); let W:= V '' U; have hx:U=V ⁻¹' W := (preimage_image_eq _ V.injective).symm; conv_rhs=> rw [hx]
   exact Eq.symm ((tempest h c).setIntegral_preimage_emb V.toMeasurableEquiv.measurableEmbedding f W)
lemma receipt (hp:Tendsto ρ (𝓝 0) (𝓝 0)) (hY:Tendsto Y (𝓝 0) (𝓝 1))(hb:∀ x,Measurable (B x)) (hμ: ∀ᶠ z:E×(I→G.Color) in 𝓝 0,∀ t:ℝ, t>0 → jacobian P (ρ z.1 + z.2) * B (t,z.1) (expLinks G I (ρ z.1+z.2)* Y z.1) = S z * Real.exp (- (F z.1 + M z)/t^2)) : Draws (tangent G I) F M S B:= by
    constructor; intro x U hu
    let J := expLinks G I; let u (t:ℝ):= ρ (t•x); let y (t:ℝ):=theme (Y (t•x)); have ht:Tendsto (fun t:ℝ=> t • x) Tested.germ (𝓝 0):= (along x).mono_left (nhdsGT_le_nhdsNE _); have hT : Tendsto (fun z:ℝ × τ=> y z.1 z.2) (Tested.germ ×ˢ 𝓝 1) (𝓝 1):= by simpa only [one_mul] using! (show Tendsto _ _ (𝓝 (1 * (1:τ))) from (show Tendsto (fun z:ℝ×τ=>z.2 *Y (z.1 •x)) _ _ from tendsto_snd.mul ((hY.comp ht).comp tendsto_fst)))
    have hr : Tendsto u Tested.germ (𝓝 0):= hp.comp ht; obtain ⟨V,hV,he⟩:= preimage_slots (T:=fun t x=> y t x) hT hu; obtain ⟨w,hw,hW⟩:= separates (G:=G) h hV; obtain ⟨L,hL,H⟩:= Metric.mem_nhds_iff.mp hμ; let q:= min (min w (small G P /2)) L; have hq:q>0:= lt_min (lt_min hw (half_pos (Ratio.small_pos h))) hL; refine ⟨q/2,half_pos hq,fun r hx=>?_⟩; let Z t:= ball (u t) r; let B' t:= y t '' (J '' Z t); let F':= ball (0:κ) q; have ht':Tendsto (fun z:ℝ × τ=> (y z.1).symm z.2) (Tested.germ ×ˢ 𝓝 1) (𝓝 1):= by simpa only [inv_one,one_mul] using! (show Tendsto (fun z:ℝ × τ=>z.2 * (Y (z.1•x))⁻¹) _ (𝓝 (1*(1:τ)⁻¹)) from tendsto_snd.mul (((hY.comp ht).comp tendsto_fst).inv)) 
    obtain ⟨A,hA,hB⟩:= preimage_slots (T:=fun t x=>(y t).symm x) ht' (pocket h (half_pos hx.1) (le_trans (half_lt_self hx.1).le (hx.2.le.trans ((half_lt_self hq).le.trans ((min_le_left ..).trans ((min_le_right ..).trans (half_lt_self (Ratio.small_pos h)).le))))));
    refine ⟨B',A,hA,?_⟩; filter_upwards [he,hB,eventually_pos,ht.eventually (Metric.ball_mem_nhds _ hL),hr.eventually (Metric.ball_mem_nhds _ (half_pos hx.1))] with t he hW' ht hX hR
    let φ:= ball (0:κ) (r/2); have hx': r < q:= hx.2.trans (half_lt_self hq); have hs : q< small G P:= lt_of_le_of_lt ((min_le_left ..).trans (min_le_right ..)) (half_lt_self (Ratio.small_pos h)); have hp: closedBall (u t) r ⊆ F':= by
       intro v hv; let T:= dist v (u t); have H': dist (u t) 0 < r/2:= hR; have h:T≤ r:=hv; have he : r<q/2:=hx.2; exact lt_of_le_of_lt (dist_triangle _ (u t) _) (by change T+_ < q; linarith only [he,H',h,hq])
    have hz : φ ⊆ Z t := by intro v hv; apply lt_of_le_of_lt (dist_triangle _ 0 _); rw [dist_comm (0:_ )]; linarith only [(Metric.mem_ball.mp hv),Metric.mem_ball.mp hR]
    have hm: MeasurableSet (J '' Z t):= interpose h hq hs.le hp
    refine ⟨(y t).toMeasurableEquiv.measurableEmbedding.measurableSet_image.2 hm,?_,?_ ,?_⟩
    · intro i hi; have hu:= hW' hi; refine ⟨(y t).symm i, Set.image_mono hz ?_,(y t).apply_symm_apply i⟩; rw [show J '' φ=chamber G I _ from image_ball (r/2) (half_pos hx.1)]; exact hu
    · apply Set.image_subset_iff.mpr ((Set.Subset.trans ?_ hW).trans he); rw [← image_ball w hw]; exact image_mono ((ball_subset_closedBall.trans hp).trans (ball_subset_ball ((min_le_left ..).trans (min_le_left ..)))) -- casts
    let O (t:ℝ):=B (t,t•x); let μ:= tangent G I; let ψ (v:κ):= u t+v; let K (v:κ):= jacobian P v*O t (y t (expLinks G I v)); let Z₀:= ball (0:κ) r; unfold beach; rw [draw_cost (P:=P) h]; change _*(∫ z in expLinks G I '' ball (u t) r,(B (t,t • x) ∘ theme (Y (t•x))) z ∂physical G I)=_; rw [ratio_cell h hq hs _ hp _ ((hb (t,t • x)).comp ((theme (Y (t•x))).continuous.measurable))] -- he expects h inserted; yes
    change _ * (∫ z in Z t,K z ∂μ)= _; rw [show (∫ z in Z t,K z ∂μ)=(∫ z in ball 0 r,K (ψ z) ∂μ) from ?_, spaces (fun z=>K (ψ z)) _ t ht.le isOpen_ball.measurableSet, Milling.ash, ←integral_const_mul]; swap; · let L: κ≃ₜκ:= Homeomorph.addLeft (u t); have hl : MeasurePreserving L μ μ:= measurePreserving_add_left ..; rw [← hl.setIntegral_preimage_emb L.toMeasurableEquiv.measurableEmbedding]; rw [show L ⁻¹' Z t=ball 0 r from ?_]; rfl; ext v; simp [L,Z, add_comm, Metric.mem_ball,dist_eq_norm_sub]
    apply setIntegral_congr_fun (disc_meas ..); intro v hv; have hM : (t•(x,v))∈ball (0:E×κ) L:= by rw [mem_ball_zero_iff,Prod.norm_def,max_lt_iff]; exact ⟨mem_ball_zero_iff.mp hX,(mem_ball_zero_iff.mp hv).trans (hx'.trans_le (min_le_right ..))⟩
    have h:= H hM t ht; unfold K; dsimp only; rw [Radial.projection_eq]; change jacobian P _ * _=_; rw [show jacobian P _ * O t _=_ from (show jacobian P (ψ (t•v))*O t (y t (J (ψ (t • v))))= S (t•(x,v))*Real.exp _ from h)]; unfold Milling.sample; change S _ * Real.exp (-(F (t•x)+ M (t•(x,v)))/_) =_; rw [neg_add,add_div,Real.exp_add,← neg_div]; ring
end Crag
end
end YM.Contacts.Lintel
