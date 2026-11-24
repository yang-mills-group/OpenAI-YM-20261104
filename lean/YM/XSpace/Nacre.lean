import YM.XSpace.Painter
/-!
# Identification of the numerical parameter as a single-line distributional convention
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Season
open Function Set Filter MeasureTheory Relief Sail Tide Lattice Trace
open Maxwell (grad)
open scoped Topology ContDiff BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{u v b:E4}(c:Shade.Cut)(R:Gleam c u v b){B C:Toe}{g h:Breeze} (H:Beam 3 B g)(K:Beam 3 C h)
include c R in
private lemma near_zone {v':E4}(a:E4)(ha:a∈tsupport (fun x=> c x))(p:range c u v'): a+u-v'≠0:=by
  intro he; unfold range at p; rw [c.tsupport_eq] at ha; have ht : ‖a‖ ≤ c.rOut:=by simpa [Metric.mem_closedBall] using ha
  have hw:u-v'= -a:=by rw [add_sub_assoc] at he; exact eq_neg_of_add_eq_zero_right he -- which
  rw [hw,norm_neg] at p; linarith [c.rOut_pos]
include c R H K in
lemma near_terms : ContDiff ℝ ∞ (green c u v b g h) ∧ HasCompactSupport (green c u v b g h):=by
  constructor
  · have ht(a b:E4):ContDiff ℝ ∞ (fun t:E4=> t+a-b):=(contDiff_id.add contDiff_const).sub contDiff_const; -- syntax
    rw [contDiff_iff_contDiffAt]; intro x; by_cases hx:x∈tsupport (fun a=> c a)
    · exact c.contDiff.contDiffAt.mul (((H.value _ (near_zone c R x hx R.uv)).comp x (ht u v).contDiffAt).mul ((K.value _ (near_zone c R x hx R.ub)).comp x (ht u b).contDiffAt))
    refine (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq ?_; filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds (show x∈ (tsupport fun a=>c a)ᶜ from hx)] with y hy; exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hy) _
  exact c.hasCompactSupport.mul_right
private lemma steps (a u v:E4): HasFDerivAt (fun t:E4=> t+u-v) (ContinuousLinearMap.id ℝ _) a:=by simpa using (((hasFDerivAt_id a).add_const u).sub_const v)
include H K in
lemma spent (t:Axis): source c t u v b g h =ᵐ[MeasureTheory.volume] (fun x=> -grad t (green c u v b g h) x):=by
  filter_upwards [clear_all u v b] with w hw; obtain ⟨_,hh,hb⟩:= hw; let f:= green c u v b g h
  have hY:= (H.value _ hh).differentiableAt (by simp); have hZ:= (K.value _ hb).differentiableAt (by simp); let z:= w+u-v; let b':= w+u-b; let d t:= c t; have hc:DifferentiableAt ℝ d w:= c.contDiff.contDiffAt.differentiableAt (n:=∞) (by simp); let L:= fderiv ℝ d w; let M:= fderiv ℝ g z; let N:=fderiv ℝ h b'; have he:= (hc.hasFDerivAt.mul ((hY.hasFDerivAt.comp w (steps w u v)).mul (hZ.hasFDerivAt.comp w (steps w u b)))).fderiv; -- synt
  change _ = -(fderiv ℝ f w (basis t)); change fderiv ℝ f w = _ at he; rw [he]; unfold source grad Analysis.D; simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,Function.comp,Pi.mul_apply]; unfold d; ring
include H K in
lemma primary_integral (t:Axis)(f:Breeze): (∫ i:E4, idle c t u v b f g h i) = -(∫ i:E4, f i * grad t (green c u v b g h) i):=by
  unfold idle; rw [← integral_neg]; refine integral_congr_ae ((spent (u:=u) (v:=v) (b:=b) c H K t).mono (fun i hi=>?_ )); dsimp only; rw [hi]; ring
-- e.g. `Opal.known_green` now applies with grad green(...) as test
end YM.XSpace.Season
