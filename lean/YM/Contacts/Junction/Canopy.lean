import YM.Contacts.Junction.Bore
/-! # Cubits branch scope & dual Taylor comparisons for qual delivery. Fix torus.
 F arb. Holds for closed cut balls. scaled. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{P : ChartRatio G} {Λ σ C v b:ℝ}{n k:ℕ}
namespace Cove
open Model.Arbor YM.Stationary
variable (F:Forest S.ratio)(T: Tube G S)(j:S.Choices)
local notation "Y" => Truck G F
local notation "E" => Anchor G c
abbrev ship (x:E) : Config G c:= input G c (settle c x)
def om (w:E×Y):= Fare.draw F (ship w.1) w.2
private def votive : Y ≃L[ℝ] LogArray G F.Free := (weld _).trans (tint G _)
local notation "τ" => F.Slice G
lemma windL : Fare.windmill F (G:=G)=⇑(votive F):=rfl
lemma paintH : Continuous (Fare.windmill F (G:=G)):= (votive F).continuous
lemma wind0 : Fare.windmill F (0:Y)=0:= (votive F).map_zero
lemma binding : Continuous (ship (G:=G) (c:=c)):= input_cont.comp (settle c).continuous
lemma floor_0 : Fare.floorG F (1:Config G c)=1 := by funext i; unfold Fare.floorG replica; split<;>rfl
lemma flooring : Continuous (Fare.floorG F (G:=G)):= continuous_pi fun i=> by unfold Fare.floorG replica; split; apply continuous_const; apply continuous_apply
lemma sum_0 : om F (0:E×Y)=1:= by unfold om draw; change release (floorG _ (ship (0:E))) (windmill _ 0)= _; unfold ship; rw [map_zero,input_zero,wind0,floor_0]; funext i; simp [release]
lemma sumH : Continuous (om F (G:=G)):= by unfold om draw; let q:= expLinks G F.Free; have he:Continuous q:= continuous_pi fun i=> G.lieExp_cont.comp (continuous_apply i); refine Continuous.mul (f:=q ∘ Fare.windmill F ∘ Prod.snd) (g:=Fare.floorG F ∘ ship ∘ Prod.fst) (he.comp ((paintH F).comp continuous_snd)) ((flooring F).comp ((binding).comp continuous_fst))
lemma time_scaled (t d:ℝ)(ht:0<t)(x:Y) : x∈closedBall 0 (d/t) ↔ ‖t • x‖ ≤ d:= by rw [mem_closedBall_zero_iff,norm_smul_of_nonneg ht.le,mul_comm,le_div_iff₀ ht]
lemma lived (r:ℝ)(t:ℝ)(ht:0<t)(x:E)(L:E→L[ℝ] Y) : staying F (L x) t (r/t) (ship x)= {v|∃ z:Y, ‖z‖≤ r∧ v= draw F (ship x) (L x+z)}:= by
   ext v; constructor; · rintro ⟨b,⟨z,hz,rfl⟩,rfl⟩; exact ⟨t•z,(time_scaled F t r ht z).mp hz,rfl⟩
   rintro ⟨z,hz,rfl⟩; let y:=t⁻¹ • z; have hu:t • y=z:= smul_inv_smul₀ ht.ne' z; exact ⟨L x+z,⟨y,(time_scaled F t r ht y).mpr (hu.symm ▸ hz),congr_arg (L x + ·) hu⟩,rfl⟩
private def hatch (U:Config G c):Y→ F.Slice G:= fun y=> expLinks G F.Free (votive F y) *floorG F U
private lemma pocket_frame {r:ℝ}(hr:0<r)(h:LocalRatio P)(x:E)(L:E→L[ℝ]Y): ∃ K:Set τ,K∈𝓝 1∧∀ᶠ t in Tested.germ, K⊆ staying F (L (t•x)) t (r/t) (ship (t•x)):= by
   let a(t:ℝ):= ship (t • x); let d:=votive F (G:=G); let U(t:ℝ): τ:=floorG F (a t); have ht : Tendsto (fun t:ℝ=> t • x) Tested.germ (𝓝 0):= (YM.Stationary.along x).mono_left (nhdsGT_le_nhdsNE _); have hv:Tendsto U Tested.germ (𝓝 1):= ((floor_0 F (G:=G)) ▸ (flooring F).tendsto 1).comp (show Tendsto a Tested.germ (𝓝 1) from (by simpa [ship,a] using! ((binding.tendsto (0:E)).comp ht)))
   let O:= expLinks G F.Free '' (d.symm ⁻¹' ball 0 (r/2))
   have ho: O∈𝓝 1:= by
      obtain ⟨s,hs,he⟩:= Metric.mem_nhds_iff.mp ((show Tendsto d.symm (𝓝 0) (𝓝 0) from (by simpa using! d.symm.continuous.tendsto 0)) (Metric.ball_mem_nhds _ (half_pos hr))); let u:=min s (PertExtension.Chart.small G P); have hu:0<u:=lt_min hs (PertExtension.Chart.Ratio.small_pos h); refine Filter.mem_of_superset (Milling.pocket (I:=F.Free) h hu (min_le_right ..)) (?_); rw [← Milling.image_ball u hu]; exact image_mono ((ball_subset_ball (min_le_left ..)).trans he)
   have hq: Tendsto (fun z:ℝ × τ=> z.2 * (U z.1)⁻¹) (Tested.germ ×ˢ 𝓝 1) (𝓝 1):= by simpa only [inv_one,mul_one] using! ((show Tendsto (fun z:ℝ × τ=> z.2) (Tested.germ ×ˢ 𝓝 1) (𝓝 (1:τ)) from tendsto_snd).mul ((hv.comp tendsto_fst).inv)); -- types?
   obtain ⟨A,hA,hS⟩:= Milling.preimage_slots (T:=fun t x=> x*(U t)⁻¹) hq ho; refine ⟨A,hA,?_⟩; let v(t:ℝ):= L (t•x); filter_upwards [hS,eventually_pos,((L.map_zero ▸ L.continuous.tendsto (0:E)).comp ht).eventually (Metric.ball_mem_nhds _ (half_pos hr))] with t ht hx hc y hy
   obtain ⟨z,hz,hj⟩:= ht hy; rw [lived F r t hx]; refine ⟨d.symm z-v t,?_ ,?_⟩; · exact (norm_sub_le ..).trans ((add_le_add (mem_ball_zero_iff.mp hz).le (mem_ball_zero_iff.mp hc).le).trans_eq (add_halves r));
   rw [add_sub_cancel]; change y = expLinks G F.Free (d (d.symm z)) * U t; rw [ContinuousLinearEquiv.apply_symm_apply,hj]; group
local notation "Ξ" => (ℝ×E)×Y
local notation "K₀" => cap G c
section view
variable {J: cap G c→ F.Slice G→ℝ}{p: (ℝ×Anchor G c) × Truck G F→ℝ}{g:cap G c→ℝ}(L:Anchor G c→L[ℝ] Truck G F) {e r:ℝ}
variable (h:Sight J g b k)(ht:P.scale=e)
include h
lemma playing (hp:LocalRatio P)(hX : ∀ x, StronglyMeasurable (J x))(hb:e>0)
    (hA : ∀ᶠ z: Ξ in 𝓝 0,z.1.1>0 → YM.Next.SectorChange.pay P (Fare.windmill F (L z.1.2+z.2)) * J (z.1.1,settle c z.1.2) (om F (z.1.2,L z.1.2+z.2))= e*Real.exp (-p z/z.1.1^2)) (x:E)(T:ℝ)(hT:0<T): ∃ (r:ℝ),0<r∧ r<T ∧∃ Q:ℝ→Set Y,(∀ᶠ t in Tested.germ,MeasurableSet (Q t) ∧ disc t r ⊆ Q t ∧ Q t ⊆ disc t T) ∧ Tested.Bill (k+1) (fun t=> ash volume 1 p t (Q t) (1,x) - (b/e)*Radial.projection 1 g t (1,settle c x)) := by
   obtain ⟨Ω,hΩ,H⟩:= h.weight ‖settle c x‖; -- h omitted
   let W(w:Ξ):= L w.1.2+w.2; let S(w:Ξ):=om F (w.1.2,W w); have hW : Tendsto S (𝓝 0) (𝓝 1):= by refine ((show Tendsto (om F (G:=G)) (𝓝 0) (𝓝 1) from sum_0 F ▸ (sumH F).tendsto 0).comp (f:=fun w:Ξ=>(w.1.2,W w)) ?_); have he:= (show Continuous (fun w:Ξ=>(w.1.2,W w)) from by unfold W; fun_prop).tendsto 0; simpa [W] using! he
   have hv: ∀ᶠ w:Ξ in 𝓝 0, Fare.windmill F (W w)∈ mouth P:= by
       have he:= (show Continuous W from by unfold W; fun_prop).tendsto 0; apply ((wind0 F ▸ (paintH F (G:=G)).tendsto 0).comp (show Tendsto W (𝓝 0) (𝓝 0) from (by simpa [W] using! he))).eventually; rw [show mouth P=ball (0:LogArray G F.Free) P.radius from (ball_pi _ hp.patch).symm]; exact Metric.ball_mem_nhds _ hp.patch -- arg extras
   obtain ⟨s,hs,H'⟩:= Metric.mem_nhds_iff.mp (hA.and (hv.and (hW.eventually (show ∀ᶠ z:τ in 𝓝 1,z∈Ω from hΩ)))); let r:= min (T/2) (s/2); have hr:0<r:=lt_min (half_pos hT) (half_pos hs); have hrt:r<T:= lt_of_le_of_lt (min_le_left ..) (half_lt_self hT); have hrs:r<s:= lt_of_le_of_lt (min_le_right ..) (half_lt_self hs); obtain ⟨K,hk,hB⟩:= pocket_frame F hr hp x L; obtain ⟨C,hC,hL⟩:= H K hk
   let Q (t:ℝ):=closedBall (0:Y) (r/t); refine ⟨r,hr,hrt,Q,eventually_pos.mono (fun t ht=>⟨measurableSet_closedBall, fun y hy=>(time_scaled F t _ ht _).mpr (mem_ball_zero_iff.mp hy).le, fun y hy=>mem_ball_zero_iff.mpr (((time_scaled F t _ ht _).1 hy).trans_lt hrt)⟩),C/e,div_nonneg hC hb.le,?_⟩
   let μ t:= staying F (L (t•x)) t (r/t) (ship (t•x)); have ht:Tendsto (fun t:ℝ=> (t,t • x)) Tested.germ (𝓝 0):= ((show Tendsto (fun t:ℝ=>t) _ _ from tendsto_id.mono_left (nhdsWithin_le_nhds (s:=Ioi _))).prodMk_nhds ((YM.Stationary.along x).mono_left (nhdsGT_le_nhdsNE _)))
   filter_upwards [eventually_pos,hB,hL,ht.eventually (Metric.ball_mem_nhds (0:ℝ×E) hs)] with t ht hK hL hw
   have hS y (hy : ‖y‖≤ r): ((t,t • x),y)∈ ball (0: Ξ) s:= by rw [mem_ball_zero_iff,Prod.norm_def,max_lt_iff]; exact ⟨mem_ball_zero_iff.mp hw,hy.trans_lt hrs⟩
   have hh y (hy:y∈ Q t):= H' (hS (t•y) ((time_scaled F _ _ ht y).mp hy)); have hm:μ t ⊆ Ω:= by rw [show μ t =_ from lived F r t ht (t•x) L]; rintro _ ⟨z,hz,rfl⟩; exact (H' (hS z hz)).2.2
   let y:= settle c x; let p':=ash volume 1 p t (Q t) (1,x); have hU:= hL y (mem_closedBall_zero_iff.mpr le_rfl) (μ t) (Fare.staying_meas ..) hm hK; let w:=ship (t • x); let g'(u:τ):= J (t,t • y) u
   have hu: beach J (μ t) t y=e*p':= by
      have hz : Module.finrank ℝ (F.Free→G.Color)= Fintype.card (Key F G):= (LinearEquiv.finrank_eq ((votive F (G:=G)).symm.toLinearEquiv)).trans (finrank_euclideanSpace ..)
      unfold beach; rw [hz]; rw [show physical _ F.Free = F.order G from rfl]; erw [Fare.cubits F P (L (t•x)) w t (r/t) g' ht hp (fun z hz=> (hh _ (mem_closedBall_zero_iff.mpr hz)).2.1) (hX _),← mul_assoc,inv_mul_cancel₀ (pow_pos ht _).ne',one_mul] -- inverse orientation
      unfold p' ash; rw [← integral_const_mul]; apply setIntegral_congr_fun measurableSet_closedBall; intro z hz; dsimp only; rw [projection_eq]; rw [Pi.one_apply,one_mul]; have h:= (hh z hz).1 ht; dsimp only at h; unfold g' y;
      rw [← map_smul (settle c)]; refine Eq.trans h (congr_arg (fun z:Ξ=> e*Real.exp (-p z/t^2)) ?_); exact Prod.ext (Prod.ext (mul_one t).symm rfl) rfl
   let G':=Radial.projection 1 g t (1,settle c x); have hG : Real.exp (-sample g (1,y) t)= G':= by unfold G' Milling.sample; rw [projection_eq,Pi.one_apply,one_mul,← neg_div];
   rw [hu,hG] at hU; apply le_of_mul_le_mul_left (a:=e) _ hb; change e*‖p'- _‖ ≤ _; rw [← Real.norm_of_nonneg hb.le,← norm_mul,mul_sub,Real.norm_of_nonneg hb.le]; change ‖_ - e*(b/e*G')‖≤_; rw [show e*(b/e*G')=b*G' by field_simp]; refine hU.trans_eq ?_; field_simp
end view
end Cove
end YM.Contacts.Junction
