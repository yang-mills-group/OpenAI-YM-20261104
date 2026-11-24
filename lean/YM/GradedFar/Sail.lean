import YM.GradedFar.Twirl
/-!
# Antenna integral derivative through S-realization

Differentiating under Ortho (Compact), same explanation as average-smooth,
with the actual slot insertion we identified already. No assumptions on rotated λ
vectors beyond the stationary budgets. Works locally in the exact orbit collar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Window
open Function Filter Set MeasureTheory Metric
open Extraction Table Spec OPE OPE.Orbits OPE.Nesting Orbits.Reader PhysMS
open Tariff
open private YM.OPE.Orbits.sample_cont YM.OPE.Orbits.smooth_section from YM.OPE.Orbits.Spin
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
attribute [local instance] OPE.Orbits.measO OPE.Orbits.borelO YM.Work.A15.compact_ortho
local instance secO : SecondCountableTopology Ortho := by
    haveI:SecondCountableTopology M4:= inferInstanceAs (SecondCountableTopology Lines)
    exact inferInstanceAs (SecondCountableTopology ↥(Matrix.unitaryGroup Axis ℝ : Set M4))
local instance hH : Orbits.haar.IsHaarMeasure:= by unfold Orbits.haar; infer_instance
local instance hP : IsProbabilityMeasure Orbits.haar := by unfold Orbits.haar; apply IsProbabilityMeasure.mk; apply Measure.haarMeasure_self
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S)(R: Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) {n:ℕ} (d:ℕ) (o:E4) (r:ℝ) (v:Fin n→S.Tag)
local notation "θ"=> F.sector.derivatives
local notation "X" => F.sector.turns
local notation "Ω"=> Reader.port R
local notation "K₁"=> target F R d o r
local notation "Y"=> illuminated F R d o r
set_option maxHeartbeats 500000 in
lemma shine (k:Ortho){x:Points n}(hx:K₁ x): ContinuousAt (fun p:Points n × Ortho=> Y v p.1 p.2) (x,k) :=by
 let w:= voices v; let p:= sites (n:=n) o r; have he:= (physics_sites o r (n:=n)).continuous; unfold illuminated; simp_rw [scatter _ R.continuum]; refine tendsto_finsetSum _ (fun i hi=> ?_)
 let T:= rotateSample (X) (Ω) i d w
 have hh:= YM.OPE.Orbits.smooth_section (Ω) R.continuum (sites o r x) o i (hx _ hi) (T k).2.1 (T k).2.2 k⁻¹
 let f(q:Points n × Ortho):= ((p q.1,o),T q.2)
 have hf: Continuous f:= ((he.comp continuous_fst).prodMk continuous_const).prodMk
    ((YM.OPE.Orbits.sample_cont (Ω) d i w R.law).comp continuous_snd)
 exact hh.continuousAt.comp (x:=(x,k)) (f:=f) hf.continuousAt
local notation "ι"=> Orbits.haar
lemma integration {x:Points n}(hx:K₁ x): Integrable (Y v x) ι := by
    let f:= Y v x; have h:Continuous f:= continuous_iff_continuousAt.mpr fun k=> (shine F R d o r v k hx).comp_of_eq
       (continuous_const.prodMk continuous_id |>.continuousAt) rfl
    exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
set_option maxHeartbeats 500000 in
lemma purifier (x:Points n)(i:Fin n×Axis)(b:ℝ)(hx:K₁ (slopePath x (Points.direction i.1 i.2) b)):
    let f(s:ℝ):= sites o r (slopePath x (Points.direction i.1 i.2) s)
    HasDerivAt (fun s=> averageV (Ω) (X) d (f s) o (voices v)) (r • averageV (Ω) (X) d (f b) o (voices (elevate F v i.1 i.2))) b:=by
 dsimp only; let t:=slopePath x (Points.direction i.1 i.2); let l:=elevate F v i.1 i.2; let g (s) (i:Ortho):= r • Y l (t s) i
 obtain he:= walking_cont x (Points.direction i.1 i.2); have hv:∀ᶠ y in 𝓝 b,K₁ (t y):= he.continuousAt.tendsto.eventually ((target_open F R o r d n).mem_nhds hx)
 obtain ⟨a,ha,hS⟩:=Metric.nhds_basis_closedBall.mem_iff.mp hv
 let L:= Metric.closedBall b a; have hm: ∀ v∈ L, K₁ (t v):=fun _ h=> hS h; let Q (z:ℝ×Ortho):=g z.1 z.2
 have hV:ContinuousOn Q (L ×ˢ Set.univ) := fun z (hz:z∈ L ×ˢ univ) => by
    rcases z with ⟨s,v⟩; exact (( ContinuousAt.const_smul ((shine F R d o r l v (hm s hz.1)).comp (x:=(s,v)) (f:=fun v:ℝ × Ortho=> (t v.1,v.2)) ( ( (he.comp continuous_fst).prodMk continuous_snd).continuousAt )) r).continuousWithinAt)
 obtain ⟨D,hD⟩:= ((isCompact_closedBall b a).prod isCompact_univ).exists_bound_of_continuousOn hV
 have hP := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=fun s=>Y v (t s)) (F':=g) (μ:=ι)
    (closedBall_mem_nhds _ ha) (hv.mono fun s hs=> (integration F R d o r v hs).aestronglyMeasurable) (integration F R d o r v hx)
    (((integration F R d o r l hx).smul r).aestronglyMeasurable) (Eventually.of_forall (fun i s hs=> hD (s,i) ⟨hs, Set.mem_univ _⟩)) (integrable_const D)
    (Eventually.of_forall (fun k b hb=> spun F R d o r k v x i b (hm _ hb)))).2
 rw [averageV, if_pos hx]
 apply HasDerivAt.congr_of_eventuallyEq (hP.congr_deriv ?_) ?_; unfold g; rw [integral_smul]; rfl
 filter_upwards [hv] with s hs; rw [averageV, if_pos hs]; rfl
end YM.Integration.GradedFar.Window
