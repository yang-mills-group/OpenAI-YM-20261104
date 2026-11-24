import YM.MatchingLedger.Gazette.Import
import YM.MatchingLedger.Cooling
import YM.PertExtension.BareChart
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The chart actually sampled by a top-step conditional SD test

All cuts in local **angles in a specified gauge**. Use native Haar; no mass comparison of the
V-conditional using extensive lower probability. Logs frozen beyond intralink patch (deterministic
convention identical at all coupling/orders, uses A). Not silently reading polynomial targets as
analytic functions on the group.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Periodical
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Books MvPolynomial Gazette Set Metric
open PertExtension.Series MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset ENNReal
variable {c f : Side} {G : Gauge} {S : StepData c f} (F : Forest S.ratio) (s : S.Choices)
    (hB : S.patch.Branches S.kernel G)(hs : InRange S) (A : ChartRatio G) (Y : Chip (Page G c))

section entrances
-- choose consistent with PertExtension on Haar fee. It is positive and exact inside.
def dial := min 1 (YM.PertExtension.Chart.small G A)
def sector (G : Gauge)(r : ℝ) : Set G.El:= G.lieExp '' ball 0 r

def boxLog := (sector G (dial A)).indicator (LocalH.snap G)
variable {A} (L : LocalRatio A)
lemma dial_small (A : ChartRatio G): dial A≤ PertExtension.Chart.small G A := min_le_right ..
include L
lemma dial_pos : 0<dial A := lt_min zero_lt_one (PertExtension.Chart.Ratio.small_pos L)
lemma cuts : dial A < A.radius := ((dial_small A).trans (min_le_left ..)).trans_lt (half_lt_self L.patch)
variable {r : ℝ}{X : G.El}{x : G.Color}
omit L
lemma sector_mono (G : Gauge) : Monotone (sector G):= fun _ _ h=> Set.image_mono (ball_subset_ball h)
lemma sector_geo (A : ChartRatio G)(he:r≤dial A) : LocalH.Geom G (sector G r) (ball 0 r):= (LocalH.geom_patch G).choose_spec.2 r ((he.trans (dial_small A)).trans (min_le_right ..))
lemma sector_open (A : ChartRatio G)(he:r≤dial A) : IsOpen (sector G r) := (sector_geo A he).1
lemma stepZone (h:x∈ball 0 r) : G.lieExp x∈ sector G r := mem_image_of_mem _ h
lemma aboard (he:r≤dial A) (h:x∈ball 0 r) : boxLog A (G.lieExp x)=x:= by
  unfold boxLog; rw [indicator_of_mem (sector_mono G he (stepZone h))]; exact (sector_geo A he).2.2.1 h
lemma pedal (he:r≤dial A) (h:X∈sector G r) : boxLog A X∈ball 0 r ∧ G.lieExp (boxLog A X)=X:= by
  obtain ⟨x,hx,rfl⟩:= h
  rw [aboard he hx]; exact ⟨hx,rfl⟩
lemma range_bound (A : ChartRatio G) (U : G.El): ‖boxLog A U‖≤1:= by
  by_cases h:U∈sector G (dial A)
  · exact (mem_ball_zero_iff.mp (pedal le_rfl h).1).le.trans (min_le_left ..)
  rw [boxLog, indicator_of_notMem h, norm_zero]; norm_num
lemma gauge_log (A : ChartRatio G) : Measurable (boxLog A) := by
  let U:= sector G (dial A); let h:=sector_geo A le_rfl
  have he : ContinuousOn (LocalH.snap G) U := fun x hx=> (((h.2.2.2.2.2.2 x hx).continuousAt).comp
    G.continuous_mat.continuousAt).continuousWithinAt
  exact ContinuousOn.measurable_piecewise (s:=U) he (g:=fun _=>0) continuousOn_const h.1.measurableSet

include L
-- consumed on one link at a time; adapted Ratio.combined proof. No product change outside ball.
theorem fraction (he:r ≤ dial A) (φ : G.El→ ℝ)(h : Measurable φ):
    (∫ x in sector G r, φ x ∂G.probHaar) = ∫ x in ball 0 r,(A.scale*A.J x)*φ (G.lieExp x) := by
  let V:= sector G r
  have hx : MeasurableSet V:= (sector_open A he).measurableSet
  have hz : ball (0:G.Color) r⊆ball 0 A.radius:= ball_subset_ball (he.trans (cuts L).le)
  let W:= fun x:G.Color=> ENNReal.ofReal (A.scale*A.J x)
  have ht : G.lieExp ⁻¹' V ∩ ball 0 A.radius= ball 0 r := by
    ext x; constructor
    · rintro ⟨⟨y,hy,h⟩,hh⟩; exact L.inject (hz hy) hh h ▸ hy
    exact fun hu=> ⟨stepZone hu,hz hu⟩
  have hw : (volume.restrict (ball 0 r)|>.withDensity W).map G.lieExp=G.probHaar.restrict V := by
    rw [← Measure.restrict_restrict_of_subset (μ:=G.probHaar) (show V⊆G.lieExp '' ball 0 A.radius from Set.image_mono hz), ← L.actual, Measure.restrict_map G.lieExp_cont.measurable hx,
        MeasureTheory.restrict_withDensity (G.lieExp_cont.measurable hx),Measure.restrict_restrict (G.lieExp_cont.measurable hx),ht] -- namespace
  rw [← hw, integral_map G.lieExp_cont.measurable.aemeasurable h.aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul₀ (μ:=volume.restrict (ball 0 r)) (show Measurable W from (L.borel.const_mul _).ennreal_ofReal).aemeasurable (Eventually.of_forall (fun x=> ENNReal.ofReal_lt_top))]
  apply setIntegral_congr_fun isOpen_ball.measurableSet; intro x h
  change (W x).toReal * φ _ = _; rw [show (W x).toReal=_ from ENNReal.toReal_ofReal (mul_nonneg L.scale.le (L.pos _ (hz h)).le)]

end entrances

section shutter
-- price gradients by using a single pre-chosen prototype in true Euclidean chart color; enough one derivative.
def lamps (G : Gauge) : ContDiffBump (0:G.Color):= ⟨1/4,1/2,by norm_num,by norm_num⟩
def shutter (G : Gauge)(r : ℝ)(x:G.Color) := lamps G (r⁻¹ • x)

@[fun_prop] lemma smooth_cut (G : Gauge)(r : ℝ) : ContDiff ℝ ∞ (shutter G r) := by unfold shutter; exact (lamps G).contDiff.comp (f:=fun x=> r⁻¹ • x) (by fun_prop)

lemma cut_low (G : Gauge)(r : ℝ)(x:G.Color): 0 ≤ shutter G r x:= (lamps G).nonneg
lemma cut_high (G : Gauge)(r : ℝ)(x:G.Color): shutter G r x ≤ 1:= (lamps G).le_one
variable {r : ℝ} (hr: 0<r)
include hr
lemma cut_one {x:G.Color} (hx:x∈ball 0 (r/4)) : shutter G r =ᶠ[𝓝 x] fun _=>1 := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  apply (lamps G).one_of_mem_closedBall; rw [mem_closedBall_zero_iff,norm_smul_of_nonneg (inv_pos.mpr hr).le,inv_mul_le_iff₀ hr]
  exact (mem_ball_zero_iff.mp hy).le.trans_eq (by unfold lamps; ring)

lemma cut_inside : tsupport (shutter G r) ⊆ closedBall 0 (r/2) := by
  apply closure_minimal _ isClosed_closedBall; intro i hi
  have hh : r⁻¹ • i ∈ Function.support (⇑(lamps G)) := hi
  rw [(lamps G).support_eq,mem_ball_zero_iff,norm_smul_of_nonneg (inv_pos.mpr hr).le, inv_mul_lt_iff₀ hr] at hh
  rw [mem_closedBall_zero_iff]; exact hh.le.trans_eq (by unfold lamps; ring)
lemma cut_interior : tsupport (shutter G r) ⊆ ball 0 r :=
  (cut_inside hr).trans (closedBall_subset_ball (half_lt_self hr))
lemma cut_compact (G : Gauge) : HasCompactSupport (shutter G r):= (isCompact_closedBall (0:G.Color) (r/2)).of_isClosed_subset (isClosed_tsupport _) (cut_inside hr)
omit hr in
lemma cut_cost (G : Gauge) : ∃ C:ℝ, 0≤C ∧ ∀ x:G.Color,‖fderiv ℝ (lamps G) x‖≤C:= by
  obtain ⟨C,H⟩:= ((lamps G).contDiff (n:=⊤)).continuous_fderiv (by simp)|>.bounded_above_of_compact_support ((lamps G).hasCompactSupport.fderiv ℝ)
  exact ⟨C, (norm_nonneg _).trans (H 0), H⟩
def dawn (G : Gauge) := (cut_cost G).choose
omit hr in
lemma dawn_pos (G : Gauge):0 ≤ dawn G:= (cut_cost G).choose_spec.1
lemma dawn_use (x v:G.Color)(hv:‖v‖≤1): ‖fderiv ℝ (shutter G r) x v‖ ≤ r⁻¹*dawn G:= by
  have hm:r≠0:=hr.ne'; have hp:0≤dawn G:= dawn_pos G
  let C: G.Color →L[ℝ] G.Color:= (r⁻¹:ℝ) • ContinuousLinearMap.id ..
  change ‖fderiv ℝ ((⇑(lamps G)) ∘ C) x v‖ ≤ _
  rw [fderiv_comp _ ((lamps G).contDiff (n:=⊤)|>.differentiable (by simp) _) C.differentiableAt,C.fderiv]
  apply (ContinuousLinearMap.le_opNorm (fderiv ℝ (lamps G) (C x)) (C v)).trans
  have hx : ‖C v‖ ≤ r⁻¹:= by change ‖(r⁻¹:ℝ) • v‖ ≤ _; rw [norm_smul_of_nonneg (inv_pos.mpr hr).le]; exact mul_le_of_le_one_right (by positivity) hv
  rw [mul_comm r⁻¹]; exact mul_le_mul ((cut_cost G).choose_spec.2 _) hx (norm_nonneg _) hp
end shutter

section walls
variable {D : ℝ}

-- tool on Taylor derivative restriction
variable {E U : Type} [NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E]
    [MeasurableSpace U]
omit [NormedSpace ℝ E]
lemma close_env {f : E→ℝ} {s:Set E}(hS : MeasurableSet s) (hp:ContinuousOn f s)(hr:0≤D) (he:∀ i∈s,‖f i‖≤D): Envelope (s.indicator f) := by
  refine ⟨ContinuousOn.measurable_piecewise hp (g:=fun _=>0) continuousOn_const hS,D,fun i=>?_⟩
  by_cases h:i∈s; rw [indicator_of_mem h]; exact he i h; rw [indicator_of_notMem h, norm_zero]; exact hr
lemma envelope_repaired {X : E→ℝ} [ProperSpace E] {L : U→E} (hp: Envelope L)(h:Continuous X): Envelope (fun x=> X (L x)):= by
  obtain ⟨a,H⟩:=hp.cost
  obtain ⟨b,hb⟩:= (isCompact_closedBall (0:E) a).exists_bound_of_continuousOn h.continuousOn
  exact ⟨h.measurable.comp hp.meas,b,fun x=> hb _ (mem_closedBall_zero_iff.mpr (H x))⟩
end walls
end YM.MatchingLedger.Periodical
