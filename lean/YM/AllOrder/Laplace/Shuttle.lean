import YM.AllOrder.Laplace.Spin
/-! # Identification of gauge-covariant operator using only the analytic collar -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Radial Tested MeasureTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical
open Lattice Wilson RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext Repeat Lapis Lantern Fare Next.Fluctuations Next.SectorChange
open ConnectedActivityE6 Blaze Brush Poll Coat
open Work.F05 Profiles AnalyticBridge.GaussianFieldAlignment Locations
open scoped BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}
variable (F: Forest S.ratio){B:ℝ → Config G f→ℝ}{P U:ℝ → Config G c}{k k':S.Choices}{R R':ℕ→ℝ}
abbrev verdict (F:Forest S.ratio)(W:ℝ→Poll.Body (Precision.Key F G))(B:ℝ → Config G f→ℝ)(P:ℝ → Config G c) (k:S.Choices) (R:ℕ→ℝ): Prop := Receipt (angle F P W (poundA F k B P)) R
section life
variable {J:Forest S.ratio} {W:ℝ→Poll.Body (Precision.Key F G)} {W':ℝ→Poll.Body (Precision.Key J G)}
   (he:Tendsto W (𝓝 0) (𝓝 0))(he':Tendsto W' (𝓝 0) (𝓝 0)) (h:Tendsto P (𝓝 0) (𝓝 1))
   (hv: verdict F W B P k R) (h':∀ t, Toll f (B t)) (hs:S.patch.Branches S.kernel G)
include hs h'
lemma booked : ∀ᶠ t in Tested.germ, let f':= poundA F k B P t; Integrable f' (F.order G) ∧ 0≤ f':= Eventually.of_forall fun t=> ⟨(env_compel F k P t (h' t) hs).integrable _, fun _i=> (Real.exp_pos _).le⟩
include h he hv
include he'
lemma confirmed (M:ℝ→ F.Slice G≃ₜ J.Slice G) (hm: Tendsto U (𝓝 0) (𝓝 1)) (hc:verdict J W' B U k' R')
   (hu:Tendsto (fun p:ℝ×F.Slice G=> M p.1 p.2) (𝓝 (0,1)) (𝓝 1))
   (hx:Tendsto (fun p:ℝ×J.Slice G=> (M p.1).symm p.2) (𝓝 (0,1)) (𝓝 1))
   (hb:∀ (t:ℝ), MeasurePreserving (M t) (F.order G) (J.order G))
   (hB : ∃ (l l' : S.Choices), ∀ (t:ℝ) (x:F.Slice G), poundA J l' B U t (M t x)=poundA F l B P t x) : R=R' := by
   obtain ⟨l,u,H⟩:= hB
   have he : ∀ᶠ x: ℝ×F.Slice G in 𝓝 (0,1), poundA F k B P x.1 x.2 = poundA J k' B U x.1 (M x.1 x.2):=by
      filter_upwards [hu.eventually (compel_same (B:=B) J k' U hs u), continuous_snd.continuousAt.eventually (compel_same (B:=B) F k P hs l)] with x h₁ h₂; rw [h₁,H]; exact h₂ x.1
   have hb' : ∀ (t:ℝ), MeasurePreserving (M t).toMeasurableEquiv (F.order G) (J.order G):=hb
   refine fan_unique hv hc (opens (M:=fun i=> (M i).toMeasurableEquiv) F h (by assumption) hm he' (Eventually.of_forall hb') hu (he.mono fun _ hp _=> hp) (booked J h' hs)) (opens (M:=fun t=> (M t).toMeasurableEquiv.symm) J hm he' h (by assumption) (Eventually.of_forall (fun t=> (hb' t).symm)) hx ?_ (booked F h' hs))
   filter_upwards [((@continuous_fst ℝ (J.Slice G) _ _).continuousAt.tendsto.prodMk_nhds hx).eventually he] with p hp t
   change poundA F k B P p.1 ((M p.1).symm p.2)=poundA J k' B U p.1 _ at hp; rw [Homeomorph.apply_symm_apply] at hp; exact hp.symm
lemma confirmed_cross (hc: verdict J W' B P k' R') : R=R':= by
   let M:=Profiles.reroute F J G
   refine confirmed F he he' h hv h' hs (fun _=> M) h hc ?_ ?_ (fun t=> Profiles.spending ..) ⟨k,k,fun t x=>compel_touch F J k P t (h' t) hs x⟩
   · have hy:Tendsto M (𝓝 1) (𝓝 1):= (rerouted_one F J) ▸ M.continuous.continuousAt.tendsto; exact hy.comp continuous_snd.continuousAt.tendsto
   have hy:Tendsto M.symm (𝓝 1) (𝓝 1):= (rerouted_one (G:=G) J F) ▸ M.symm.continuous.continuousAt.tendsto; exact hy.comp continuous_snd.continuousAt.tendsto
omit he'
lemma confirmed_color (u:ℝ→Site c→G.El)(x:G.El)(hx:Tendsto u (𝓝 0) (𝓝 (fun _=> x)))
   (hU: U = fun t => gauge (u t) (P t)) (hu : Tendsto U (𝓝 0) (𝓝 1))
   (hw':ℝ→Poll.Body (Precision.Key F G))(hw:Tendsto hw' (𝓝 0) (𝓝 0))(hc:verdict F hw' B U k' R') : R=R':=by
      have he0 (v:ℝ→Site c → G.El)(x:G.El) (hv:Tendsto v (𝓝 0) (𝓝 (fun _=>x))): Tendsto (fun q:ℝ× F.Slice G=> fitted F (v q.1) q.2) (𝓝 (0,1)) (𝓝 1) := by
         let s:=(fitted (G:=G) F); let A:=(F.Slice G);
         have hp: Tendsto (fun p:(Site c→G.El) × A=> s p.1 p.2) (𝓝 ((fun _=> x),1)) (𝓝 1):= by nth_rw 2 [← fitted_op F x]; exact (fitted_live (G:=G) F).continuousAt.tendsto
         have he : Tendsto (fun p:ℝ × A=> v p.1) (𝓝 (0,1)) (𝓝 (fun _=> x)):= hv.comp continuous_fst.continuousAt.tendsto
         have hY : Tendsto Prod.snd (𝓝 ((0:ℝ),(1:F.Slice G))) (𝓝 (1:F.Slice G)):= continuous_snd.continuousAt.tendsto; have hz:= he.prodMk_nhds hY; change Tendsto ((fun p : _ × A=> s p.1 p.2) ∘ fun q => (v (Prod.fst q),q.2)) _ _; exact (hp.comp hz)
      refine confirmed F he hw h hv h' hs (fun t=> fitted F (u t)) hu hc (he0 u x hx) ?_ (fun t=> fitted_pays ..) ⟨k,k,fun t v=> (hU.symm ▸ compel_color F k P t (h' t) hs u v)⟩
      simpa only [fitted_inv] using he0 (fun t=>(u t)⁻¹) (x⁻¹) hx.inv
lemma confirmed_pulled (s:Signed)(x:Site c)
   (hU:U=pull s x ∘ P)(hu:Tendsto U (𝓝 0) (𝓝 1))
   (hw':ℝ→Poll.Body (Precision.Key (Locations.forest s x F) G))(hw:Tendsto hw' (𝓝 0) (𝓝 0))(hc:verdict (Locations.forest s x F) hw' B U k' R') : R=R':=by
      let M:= jointTour (G:=G) F s x
      have ht:M 1=1:= at_one F ..; have hp:M.symm 1=1:=by rw [←ht]; exact M.symm_apply_apply _
      subst U; apply confirmed F he hw h hv h' hs (fun _=>M) hu hc ((show Tendsto M (𝓝 1) (𝓝 1) from ht ▸ M.continuous.continuousAt.tendsto).comp continuous_snd.continuousAt.tendsto) ((show Tendsto M.symm (𝓝 1) (𝓝 1) from hp ▸ M.symm.continuous.continuousAt.tendsto).comp continuous_snd.continuousAt.tendsto) (fun t=> saving ..) ⟨S.withinChoice s x k,k,fun t U=> compel_shift F k P t (h' t) hs s x U⟩
end life
end YM.AllOrder.Laplace
