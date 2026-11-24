import YM.FVA2.Hearth.Choice
import YM.FVA2.Hearth.Stables
import YM.Progress.STATIONARY_SCENES.Frames
import YM.Push.SECTOR_MEASURE.Gauges
import YM.Pert.Kinetic.Curl
/-!
 # Joint predictor tag case on the even inversion regulator

 Although the physical Wilson PT rule only uses the germ where ALL predictor
 choices give exactly the same costs, it's possible to use the optional actual
 likelihoods `StepData.likelihood` from the finite torus (on constrained
 fields, **a single vector of tags** over the epoch, reused across all factors).
 The sums here use one such auxiliary extension even on unmasked units. Branches
 covariance applies on this entire extension, while exact predictor inversion away
 from flat/at all tags isn't asserted (each predictor is evaluated on ANY input,
 from the established chart map `atStep` on independent orbit coordinates).
 Moment readings will use only the flat-saddle histories of this same prescription.
 No comparison of a normalized object taking steps on the cover is inferred;
 all fields subject to the inversion condition, no harmonic gluons, penalty
 *per independent orbit bond*. Not using the `StepData.density` whose geometry is
 the unrestricted full torus.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Embr
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Finset MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth RGComparison.Core16
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {c f n:Side} {L:Fabric G n}

-- likelihood of ONE joint Capsule sampled conditionally on these precise earlier
-- links at each step, including holonomies in S on this geometry. Fixed given Cloth.
def poll {n:Side}(L:Fabric G n)(x: L.LinksOn)(t: Clan L) : ℝ := match L with
 | .endcap _ _ => 1
 | .layer S H b hf L=> S.likelihood (liftLinks ((layer S H b hf L).principal x)) (show S.Choices×Clan L from t).1 * poll L (future S H b hf L x) (show S.Choices× Clan L from t).2

variable (L)
lemma total {n:Side}(L:Fabric G n)(x:L.LinksOn): ∑ t,poll L x t=1:= by
 cases L with
 | endcap n h=> change (∑ _ : Unit,(1:ℝ)) = _; rw [sum_const]; simp only [card_univ]; erw [Fintype.card_unique,nsmul_eq_mul,Nat.cast_one,one_mul]
 | layer S H b hf L=>
   unfold poll; change (∑ t:S.Choices× Clan L,S.likelihood _ t.1 * Embr.poll L _ t.2) = _; rw [Fintype.sum_prod_type]; simp_rw [←mul_sum,Embr.total L,mul_one,StepData.chosen S H]
termination_by structural L
lemma steady_vote {n:Side}(L:Fabric G n)(x:L.LinksOn)(t): 0≤poll L x t:= by
 cases L with
 | endcap=> exact zero_le_one
 | layer S _ _ _ L=> exact mul_nonneg (StepData.likelihood_pos S ..) (steady_vote L ..)
termination_by structural L
lemma flexible {n:Side}(L:Fabric G n)(t:Clan L): Measurable (fun x=>poll L x t):= by
 cases L with
 | endcap=> exact measurable_const
 | layer S H b hf L=> exact Measurable.mul ((StepData.likelihood_meas S H _).comp ((Orb.lift_cont G).measurable.comp (principal_cont (layer S H b hf L)).measurable)) ((flexible L _).comp (future_cont S H b hf L).measurable)
termination_by structural L

lemma motion {n:Side}(L:Fabric G n)(x:L.LinksOn)(g: Vertex n→G.El)(t:Clan L): poll L (L.loom.spin g x) t=poll L x t:= by
 cases L with
 | endcap=>rfl
 | @layer c f S H b hf L=>
    let T:= layer S H b hf L; unfold poll; rw [spin_future,spin_main]; change S.Choices × Clan L at t
    exact congr_arg₂ (· * ·) ((congr_arg (fun x=> S.likelihood x t.1) (show liftLinks (even_spin (g∘track) (T.principal x))=Lattice.gauge (g∘ track) (liftLinks (T.principal x)) from funext fun i=> (Orb.path_law (g∘track) (T.principal x) (track_even g) i).symm)).trans (Push.SectorMeasure.choice_gauge H _ _ _).1) (motion L _ _ _)
termination_by structural L

lemma write_off (S:StepData c f)(H:S.patch.Branches S.kernel G): ∀ᶠ u : Wilson.Config G f in 𝓝 1,∀ t:S.Choices, S.likelihood u t=(Fintype.card S.Choices:ℝ)⁻¹:= by
 let V(u:Wilson.Config G f) : Push.In G f:= Pert.Kinetic.lift1 (fun i=> G.plog (G.mat (u i)))
 have hV:ContinuousAt V 1:= by
   refine continuousAt_pi.mpr fun i=>?_
   let f0 (u:Wilson.Config G f):= G.mat (u (i.1,Exterior.axisEquiv.symm i.2)); have HE: ContinuousAt G.plog (f0 1):=G.plog_diff.continuousAt
   exact HE.comp ((G.continuous_mat.comp (continuous_apply (i.1,Exterior.axisEquiv.symm i.2))).continuousAt)
 have he: V 1=0:= funext (fun i=> by change G.plog (G.mat 1) = 0; simp)
 have hv:Tendsto V (𝓝 1) (𝓝 0):= he ▸ hV.tendsto
 have hm (i:Lattice.Edge (Lattice.Site f)): ∀ᶠ u : Wilson.Config G f in 𝓝 1, represent (V u) i=u i := by
     filter_upwards [((continuous_apply i).tendsto (1:Wilson.Config G f)).eventually G.plog_right] with u hu
     unfold represent RG.increment V; rw [Pert.Kinetic.back_wave]; simpa using! hu
 filter_upwards [hv.eventually (Progress.StationaryScenes.likelihood_here H),eventually_all.mpr hm] with x h hx; rwa [funext hx] at h
lemma level_money {n:Side}(L:Fabric G n): ∀ᶠ u in 𝓝 (1:L.LinksOn),∀ k,poll L u k=poll L 1 k:= by
 cases L with
 | endcap=> exact Filter.Eventually.of_forall fun u k=> rfl
 | @layer c f S H t hf L=>
    let T:= layer S H t hf L; let k:L.LinksOn:=1
    let E : T.LinksOn → Wilson.Config G n := liftLinks ∘ T.principal
    have hE : E 1=1:= lift_one
    have hv : ∀ᶠ x:T.LinksOn in 𝓝 1,∀ t,S.likelihood (E x) t=(Fintype.card S.Choices:ℝ)⁻¹:= (( (hE ▸ ((Orb.lift_cont G).comp T.principal_cont).tendsto 1) : Tendsto E (𝓝 1) (𝓝 1))).eventually (write_off S H)
    have hk:= hm hv
    filter_upwards [hv,((future_cont S H t hf L).tendsto 1).eventually (level_money L)] with u hu hc v; unfold poll; exact congr_arg₂ (· * ·) ((hu _).trans (hk _).symm) (hc _)
termination_by structural L
where
 hm {n} {L:Fabric G n}{p:L.LinksOn→Prop}(h:∀ᶠ a in 𝓝 (1:L.LinksOn),p a):p 1:= Filter.Eventually.self_of_nhds h
end YM.FVA2.Embr
