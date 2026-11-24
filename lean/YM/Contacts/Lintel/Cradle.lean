import YM.Contacts.Lintel.Hill
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
variable {M F K J: E×V→ℝ}
open Tested
variable [MeasurableSpace E][MeasurableSpace V][BorelSpace E][BorelSpace V]
variable (μ:Measure V)[μ.IsNegInvariant][μ.HasTemperateGrowth]
include μ
omit μ [μ.IsNegInvariant][μ.HasTemperateGrowth] in
lemma normalized {f:E→ℝ}(h:AnalyticAt ℝ f 0): ∃ g: E→ℝ, Measurable g ∧ f=ᶠ[𝓝 0] g:= by -- omit μ
   obtain ⟨s,hs,hy⟩:= Metric.mem_nhds_iff.mp (h.eventually_analyticAt); let V:=ball (0:E) s; have ht : ContinuousOn f V:= fun x hx=> (hy hx).continuousAt.continuousWithinAt; exact ⟨V.indicator f, ht.measurable_piecewise continuous_const.continuousOn isOpen_ball.measurableSet, (show ∀ᶠ i in 𝓝 0,i∈V from isOpen_ball.mem_nhds (mem_ball_self hs)).mono fun x hx=> (indicator_of_mem hx _).symm⟩
omit μ [μ.IsNegInvariant][μ.HasTemperateGrowth] in
private lemma jets_eq (h: F=ᶠ[𝓝 0] M)(x:E×V)(n:ℕ) : jet F n x=jet M n x:= by unfold jet; rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]
private lemma weak (hf:AnalyticAt ℝ F 0)(hk: AnalyticAt ℝ K 0)(hp:∀ y, jet F 0 y=0)(hu:∀ y,jet F 1 y=0){c R b:ℝ} (hc:0<c)(hz:Hilly F (c+c) R b) : ∃ δ>0,∀ (r:ℝ),0 < r→ r < δ → ∀ x∈closedBall (0:E) R,Tested.Bill 3 (fun t=> ash μ K F t (disc t r) x - Zone.eval (Milling.mural μ K F) 2 t x):= by
   obtain ⟨f,hf',he⟩:= normalized hf; obtain ⟨u,hu',hx⟩:= normalized hk; have Hs:=hf.congr he; have hk':=hk.congr hx; have hg n y : jet f n y=jet F n y:= jets_eq he ..|>.symm; have hp' n y : jet u n y=jet K n y:= jets_eq hx ..|>.symm
   have hS : Hilly f (c+c) R b:= by intro x hh y; rw [hg]; exact hz x hh y
   obtain ⟨δ,hδ,H⟩:= perspective μ (serenity Hs (fun _=> (hg ..).trans (hp _)) (fun _=> (hg ..).trans (hu _))) hk'.contDiffAt hu' hf' hc hS 2; obtain ⟨q,hq,hV⟩:= Metric.mem_nhds_iff.mp (he.and hx); refine ⟨min δ q,lt_min hδ hq,fun r hr he_priority x ht=>?_⟩; let y(t):= disc t r (E:=V); obtain ⟨D,hD,hz⟩:= H r hr; have hE (x:E): ∀ᶠ t in Tested.germ, t•x∈ball 0 q:= ((show Continuous (fun t:ℝ=>t•x) by fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (isOpen_ball.mem_nhds (zero_smul ℝ x|>.symm ▸ mem_ball_self (x:=(0:E)) hq)); refine ⟨D,hD,?_⟩; filter_upwards [hE x,hz] with t hp hz
   have he':(ash μ K F t (y t) x)=(ash μ u f t (y t) x):= by
      unfold ash; apply setIntegral_congr_fun (disc_meas ..); intro v hv; have hhx:t•x∈ball 0 q:=hp; have heq:=hV (show t• (x,v) ∈ ball 0 q from (by rw [mem_ball_zero_iff,Prod.norm_def,max_lt_iff]; exact ⟨mem_ball_zero_iff.mp hhx,(mem_ball_zero_iff.mp hv).trans (he_priority.trans_le (min_le_right ..))⟩)); dsimp only; rw [projection_eq,projection_eq, (show _=(u _) from heq.2),(show _= f _ from heq.1)]
   change ‖ash _ _ _ t (y t) _-_‖≤_; rw [he']; have hr' d (hh:d≤2): Milling.mural μ K F d x=Milling.mural μ u f d x := integral_congr_ae (Eventually.of_forall fun y=>by interval_cases d <;> simp only [normTerm,kernel,theme0,theme1,theme2,hx.eq_of_nhds,hp',hg])
   convert (hz (y t) (disc_meas ..) (subset_refl _) (preimage_mono (ball_subset_ball ((he_priority.trans_le (min_le_left ..)).le : r≤δ))) x ht).2 using 1; all_goals first | omega | exact (by change r < _ at he_priority; linarith)| (unfold Zone.eval; simp_rw [Finset.sum_range_succ,Finset.sum_range_zero,hr' 2 le_rfl,hr' 0 (by decide),hr' 1 (by decide) ]) -- need named he' not shadow
private lemma estimate_merge (h:Paired F M K J)(R:ℝ): ∃ q>0,∀ r>0,r<q→∀ x∈closedBall (0:E) R,Bill 3 (fun t=> ash μ K F t (disc t r) x-ash μ J M t (disc t r) x-t^2*(Milling.mural μ K F 2 0-Milling.mural μ J M 2 0)):= by
   obtain ⟨c,hc,C,hf,hm⟩:=h.slants R; obtain ⟨s,hs,hP⟩:= weak μ h.core h.K0 (fun _=> (jet_zero ..).trans h.new.base0) h.new.base1 hc hf; obtain ⟨d,hd,hQ⟩:= weak μ h.axis h.J0 (fun _=> (jet_zero ..).trans h.old.base0) h.old.base1 hc hm;
   refine ⟨min s d,lt_min hs hd,fun r hr hv x hx=>?_⟩; convert bill_add (hP r hr (lt_of_lt_of_le hv (min_le_left ..)) x hx) (bill_neg (hQ r hr (lt_of_lt_of_le hv (min_le_right ..)) x hx)) using 1; funext t; rw [← breeze h μ x]; unfold Zone.eval; simp only [Finset.sum_range_succ,Finset.sum_range_zero, smul_eq_mul,Pi.add_apply, Pi.neg_apply, bridal h μ x 0 (by decide), bridal h μ x 1 le_rfl]; ring
-- comparing to FULL homogeneous reference with graph constant.
private lemma pfocus (hf : ∀ᶠ x:E in 𝓝 0,∀ y:V, (∀ t:ℝ, M (x,t•y)=t^2*M (x,y)) ∧ J (x,y)=J (x,0))(x:E) : ∀ᶠ t in Tested.germ,∀ y:V, projection J M t (x,y)=J (t•x,0)* Real.exp (- M (t•x,y)) := by
   filter_upwards [eventually_pos,(along x).eventually hf|>.filter_mono (nhdsGT_le_nhdsNE _)] with t ht hv y; rw [projection_eq,show t•(x,y)=(t•x,t•y) from rfl,(hv (t•y)).2,(hv y).1]; field_simp
-- only tasks in Param
private lemma topTail {c:ℝ}(hc:0<c){r:ℝ}(hr:0<r)(k:ℕ){F:ℝ→V→ℝ}{C:ℝ}(hC:0≤C) (hf:∀ᶠ t in Tested.germ, Measurable (F t) ∧ ∀ v, ‖F t v‖ ≤ C*Real.exp (-c*‖v‖^2)) : (∀ᶠ t in Tested.germ, Integrable (F t) μ) ∧ Bill k (fun t=> ∫ x in (disc t r)ᶜ, F t x ∂μ):= by
   let D:= C*r⁻¹^k; have hD:0 ≤ D:=(by unfold D; positivity); refine ⟨hf.mono (fun t h=> ((bill_integrable μ 0 hc).const_mul C).mono' h.1.aestronglyMeasurable (Eventually.of_forall (fun x=>by simpa [Radial.bill] using h.2 x))),D*(∫ x:V,Radial.bill k c x ∂μ),mul_nonneg hD (integral_nonneg fun _=> bill_nonneg ..),?_ ⟩; filter_upwards [hf,eventually_pos] with t ho ht; refine le_trans (sized μ k hc (mul_nonneg (pow_nonneg ht.le k) hD) ?_ ho.1.aestronglyMeasurable).2 ?_; swap; · exact le_of_eq (by ring)
   filter_upwards [ae_restrict_mem (disc_meas (E:=V) t r|>.compl)] with x hx;
   have hz : r≤ t*‖x‖:= not_lt.mp ((show x∉disc t r from hx) ∘ (disc_mem ht.le r x).2); have hk : 1 ≤ t*r⁻¹*(1+‖x‖):= by field_simp; linarith; -- syntax
   exact (ho.2 x).trans ((le_mul_of_one_le_right (by positivity : 0≤C*Real.exp (-c*‖x‖^2)) (one_le_pow₀ hk)).trans_eq (by unfold D Radial.bill Radial.zone; rw [mul_pow, mul_pow]; ring))
lemma lantern (h:Paired F M K J) (hf : ∀ᶠ x:E in 𝓝 0,Measurable (fun y:V=>M (x,y)) ∧ ∀ y:V,(∀ t:ℝ, M (x,t•y)=t^2*M (x,y)) ∧ J (x,y)=J (x,0))(hl : ∃ c:ℝ,0<c ∧ ∀ᶠ x:E in 𝓝 0,∀ y:V,c*‖y‖^2 ≤ M (x,y))(R:ℝ): ∃ q>0,∀ r>0,r< q→ ∀ x∈closedBall (0:E) R,Bill 3 (fun t=>ash μ K F t (disc t r) x - J (t•x,0)*(∫ y:V,Real.exp (-M (t•x,y)) ∂μ)- t^2*(Milling.mural μ K F 2 0-Milling.mural μ J M 2 0)):= by
   obtain ⟨c,hc,hC⟩:=hl; obtain ⟨q,hq,H⟩:= estimate_merge μ h R; refine ⟨q,hq,fun r hr hv x hx=> ?_⟩; let f (t:ℝ)(y:V):= projection J M t (x,y); have hy:= pfocus (μ:=μ) (hf.mono fun _ h=>h.2) x; let J'(t:ℝ):=J (t•x,0); let y(t:ℝ)(v:V):= M (t•x,v); let g t:= ∫ v,(Real.exp (-y t v)) ∂μ; have ht:Tendsto (fun t:ℝ=> t•x) Tested.germ (𝓝 0):= (along x).mono_left (nhdsGT_le_nhdsNE _); let u:= ‖J 0‖+1; have hu:0≤u:=by unfold u; positivity
   have hh:Tendsto J' Tested.germ (𝓝 (J 0)):= h.J0.continuousAt.tendsto.comp (ht.prodMk_nhds tendsto_const_nhds) -- g
   have he : ∀ᶠ t in Tested.germ, Measurable (f t)∧ ∀ v, ‖f t v‖≤u*Real.exp (-c*‖v‖^2):= by
      filter_upwards [hy,ht.eventually hf,ht.eventually hC, hh.norm.eventually_le_const (show ‖J 0‖<u from lt_add_one _)] with t hp hf hC hg; rw [show f t=(fun y=>_) from funext hp]; exact ⟨measurable_const.mul (hf.1.neg.exp),fun v=> by rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]; exact mul_le_mul hg (Real.exp_monotone (by linarith only [hC v])) (Real.exp_pos _).le hu ⟩
   obtain ⟨ht',D,hD,hS⟩:= topTail μ hc hr 3 hu he; obtain ⟨z,hz,hZ⟩:= H r hr hv x hx; refine ⟨z+D,add_nonneg hz hD,?_⟩; filter_upwards [hZ,hy,hS,ht'] with t hZ he hS hh; set p:=t^2* (Milling.mural μ K F 2 0-Milling.mural μ J M 2 0); let s:= disc t r (E:=V); let G:=∫ x in sᶜ,f t x ∂μ; let h': ash μ J M t s x+G=(J' t)*g t:=by
      rw [(show ash μ J M t s x+G=∫ y,f t y ∂μ from integral_add_compl (disc_meas ..) hh),show f t=(fun y=> J' t*Real.exp (-M (t•x,y))) from funext he,integral_const_mul]
   change ‖ash μ K F t s x-J' t*g t-p‖≤_; rw [←h',show ash _ _ _ _ _ _- _-p=(ash μ K F t s x-ash μ J M t s x-p) - G by abel]; refine (norm_sub_le ..).trans ((add_le_add hZ hS).trans_eq (add_mul z D _).symm)
end Crag
end
end YM.Contacts.Lintel
