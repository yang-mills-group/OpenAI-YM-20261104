import YM.GapsContact.Jost.Aligned
/-!
# Analytic Jost extension on real chambers. Keep both choices of blades and measurement frames
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Jost
open Function Filter Set Mink Mink.Poincare Boundary Boundary.Surface Bid Analysis MeasureTheory Spec Spin Extraction Next.BOUNDARY
open Ascent EveryPhase Tunnel
open scoped Topology BigOperators InnerProductSpace Classical ContDiff NNReal
universe u
variable {n:ℕ} {G:Gauge}

section Body
variable {L:Register G}{S:Table L}{D:∀ n,Blanket n} {W:Surface S}(X:W.Aurora D)
open Probe
-- reuse basis/C19 proof allowing heterogeneous grades
private def emitAt (X : W.Aurora D) (x : Full n) :
    MultilinearMap ℂ (fun _ : Fin n => S.Union) ℂ :=
  let A : Distn (Points n) →ₗ[ℂ] ℂ :=
    { toFun u := ((pref (Points n))⁻¹ : ℂ) * Distn.fourier u (X.lens n x)
      map_add' u v := by simp [mul_add]
      map_smul' c u := by simp [mul_left_comm] }
  A.compMultilinearMap (W.W n)

/- Separate slot labels move holomorphically at a fixed finite degree.
Expand in that finite basis to keep `FullBody.hol`'s fixed-label
hypothesis. In particular no claim about a norm on `Union`. -/
private lemma emit_analytic {F:Waves S} (hX : X.FullBody F) {d : Fin n → ℕ} (u : ∀ i:Fin n, ℂ → S.Field (d i))
    (w : ℂ → Full n) (z : ℂ) (hu : ∀ i, AnalyticAt ℂ (u i) z)
    (hw : AnalyticAt ℂ w z) (hin : w z ∈ tube n) :
    AnalyticAt ℂ (fun b => X.emit (fun i => S.pin (d i) (u i b)) (w b)) z := by
  classical
  let B := fun i => Module.finBasis ℂ (S.Field (d i))
  have he : (fun b => X.emit (fun i => S.pin (d i) (u i b)) (w b)) =
      fun b => ∑ j : (∀ i:Fin n, Fin (Module.finrank ℂ (S.Field (d i)))),
        (∏ i, (B i).coord (j i) (u i b)) • X.emit (fun i => S.pin (d i) (B i (j i))) (w b) := by
    funext b
    have hp : (fun i => S.pin (d i) (u i b)) =
        fun i => ∑ j, (B i).coord j (u i b) • S.pin (d i) (B i j) := by
      funext i
      conv_lhs => rw [← (B i).sum_repr (u i b), map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
      rfl
    rw [hp]
    change emitAt X (w b) _ = _
    rw [MultilinearMap.map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact (emitAt X (w b)).map_smul_univ _ _
  rw [he]
  apply ContDiffAt.analyticAt
  refine ContDiffAt.sum (fun j hj => ?_)
  apply ContDiffAt.mul
  · refine contDiffAt_prod (fun i hi => ?_)
    let A : S.Field (d i) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap ((B i).coord (j i))
    exact ((A.analyticAt _).comp (hu i)).contDiffAt
  exact ((hX.hol n _ _ hin).comp hw).contDiffAt

end Body

variable {C:Family G}{f:Extraction.Order} {S:Table C.book}
variable {F:Final C f S} (L:Almanac F) (i:Survey F) {D:∀ n,Blanket n}(X:(Survey.reads L i).world.Aurora D)
variable (P:Scheme n){d: Fin n → ℕ}(B:∀ j:Fin n, Blade F (d j) P.e)(v:∀ j:Fin n,S.Field (d j)){r:ℝ}(hr:0<r)

def panel (r:ℝ)(z:Full n):=weather X (fun j=> S.pin _ (fly F (d j) P (B j) (v j))) r (reach P.g P.e P.speed z)
include hr in
lemma panel_analytic :AnalyticOnNhd ℂ (panel L i X P B v r) P.zone:=fun _ ht=> ((hollow X (observe L i X).2 _ _ hr) _ (P.fits ht)).comp (f:=reach P.g P.e P.speed) (ContinuousLinearMap.analyticAt ..)

lemma enters_tube (r:ℝ)(hr:0<r){z:Full n}(hz:z∈tube n): (r:ℂ) • z∈tube n:=by
    change shade _∈fields n; rw [shade_scale]; exact swell hz hr
-- reusing the actual Lorentz contour data. No assumed matrix growth near window.
lemma turning (v:Fin n→ S.Union) (g:Lorentz){z:Full n}(hz:z∈tube n): X.emit v z=X.emit (fun j=> F.action.spin.rail g (v j)) (rect g z):=by
    obtain ⟨Y,hY,h⟩:= observed L i
    have hp:= neon_any h X; exact Integrated.reconstructionArcs.cP _ _ D X Y.lift hp.1 (observe L i X).1 h.rotates hp.2 n v g z hz

include hr
lemma panel_reached :EqOn (panel L i X P B v r) (weather X (fun j=> S.pin _ (v j)) r) (P.zone∩tube n):=by
    intro z hz
    let Z:= straighten P.g ((r:ℂ) • z); have hZ : Z∈tube n:= rect_open _ _ (enters_tube r hr hz.2)
    let y:=fun j=> F.action.spin.shell (d j) P.g (v j); let Q(s:ℂ):= X.emit (fun j=> S.pin _ ((B j).U s (y j))) (curve P.e s Z); let T:= X.emit (fun j=> S.pin _ (y j)) Z
    let γ(b:ℝ):= (b:ℂ)*Complex.I
    have hh(s):curve P.e (γ s) Z= (r:ℂ) • reach P.g P.e s z:=by unfold Z reach; rw [map_smul,map_smul]; rfl
    suffices EqOn Q (fun _=>T) (γ '' Icc 0 P.speed) by
       unfold panel weather; rw [← hh]; change Q (γ _)=_; rw [this ⟨_,right_mem_Icc.mpr P.armed.le,rfl⟩,turning L i X (fun j=> S.pin _ (v j)) P.g (enters_tube r hr hz.2)]; simp_rw [F.realization.qt.letters.ties]; rfl
    have H : AnalyticOnNhd ℂ Q (γ '' Icc 0 P.speed) :=by
       rintro s ⟨t,ht,rfl⟩
       apply emit_analytic X (observe L i X).2 (d:=d) (fun j s=> (B j).U s (y j)) (fun z=> curve P.e z Z) (γ t) (fun i=> (B i).attune (y i) _ (Set.mem_univ _))
       · exact analytic_boost_path P.e Z (γ t) -- lambda defeq?
       rw [hh]; exact enters_tube r hr (P.onto z hz.1 hz.2 t ht)
    refine H.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const (isPreconnected_Icc.image γ (by unfold γ; fun_prop)) (show (0:ℂ)∈ γ '' _ from ⟨0,left_mem_Icc.mpr P.armed.le,by simp[γ]⟩) ?_
    refine oftReal fun t=>?_
    unfold Q; simp_rw [Blade.line,curve_augments,augment_real,← F.realization.qt.letters.ties]
    exact (turning L i X _ (P.e.boost t) hZ).symm
lemma panel_overlap (Q:Scheme n)(T:∀ j,Blade F (d j) Q.e){z:Full n}(hp:z∈P.zone)(hq:z∈Q.zone)(hl: shade z∈shores n) : EqOn (panel L i X P B v r) (panel L i X Q T v r) (P.zone∩Q.zone):=by
   let U:=P.zone∩Q.zone; let W:= tube n
   have hu:IsOpen U:=P.clear.inter Q.clear
   obtain ⟨x,hx,hX⟩:= mem_closure_iff.mp (closure_tube z hl) U hu (Set.mem_inter hp hq)
   apply ((panel_analytic L i X P B v hr).mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq ((panel_analytic L i X Q T v hr).mono inter_subset_right) (P.arch.inter Q.arch).isPreconnected hx
   filter_upwards [P.clear.mem_nhds hx.1,Q.clear.mem_nhds hx.2,(south n).mem_nhds hX] with y hy1 hy2 hY using (panel_reached L i X P B v hr (Set.mem_inter hy1 hY)).trans (panel_reached L i X Q T v hr (Set.mem_inter hy2 hY)).symm

open Metric in
-- price extends tested identity to EVERY test in chart (not only shrinking after r/d/x etc.)
lemma real_panel (φ:Joint n)(hx:HasCompactSupport ⇑φ)(hk:∀ x∈tsupport φ, glow x 0∈ P.zone):
   Integrable (fun x=> panel L i X P B v r (glow x 0)*φ x) ∧
   (Survey.reads L i).world.W n (fun j=>S.pin _ (v j)) (TraceExtension.condense r⁻¹ φ) = ∫ x,panel L i X P B v r (glow x 0)*φ x:=by
   let H:=panel L i X P B v r; let U:=weather X (fun j=> S.pin _ (v j)) r; let k:= tsupport φ; let Y:= (fun p:Points n × Points n=> glow p.1 p.2)
   have hK : IsCompact k:=hx
   have hp (x) (hx:x∈k) := panel_analytic L i X P B v hr (glow x 0) (hk x hx);
   have hc(y:Points n):Continuous (fun x:Points n=>glow x y):= (home n).comp (continuous_id.prodMk continuous_const)
   have hU(x:Points n)(hx:x∈ fields n): Continuous fun y:Points n=> U (glow y x) := (hollow X (observe L i X).2 _ r hr).continuousOn.comp_continuous (hc x) (fun p=> by simp [tube,hx])
   have hm(x:Points n)(he:x∈k) : ContinuousAt (fun x=> H (glow x 0)) x:=(hp x he).continuousAt.comp (f:=fun x:Points n=> glow x 0) (hc 0).continuousAt
   constructor
   · have h:Continuous fun x=> H (glow x 0)*φ x:=by
         apply continuous_iff_continuousAt.mpr; intro x; by_cases ht:x∈k
         · exact (hm x ht).mul φ.continuous.continuousAt
         refine continuousAt_const.congr_of_eventuallyEq (f:=fun _=>(0:ℂ)) ?_
         filter_upwards [(isClosed_tsupport ⇑φ).isOpen_compl.mem_nhds ht] with y hy; rw [image_eq_zero_of_notMem_tsupport (by exact hy : y∉ tsupport ⇑φ),mul_zero]
     exact h.integrable_of_hasCompactSupport hx.mul_left
   obtain ⟨A,A',ha,ha',ho,hh,hy⟩:= generalized_tube_lemma hK (isCompact_singleton (x:=(0:Points n))) (P.clear.preimage (show Continuous Y from home n)) (by rintro ⟨x,t⟩ ⟨hx,hh : t∈({0}:Set (Points n))⟩; change glow x t∈P.zone; rw [Set.mem_singleton_iff.mp hh]; exact hk x hx)
   obtain ⟨σ,hσ,hR⟩:=Metric.mem_nhds_iff.mp (ha'.mem_nhds (hh (Set.mem_singleton _)))
   let Z:= closedBall (0:Points n) (σ/2); have hc' : Y '' (k ×ˢ Z)⊆P.zone:=by
      rintro q ⟨p,hp,rfl⟩; exact hy ⟨ho hp.1,hR (closedBall_subset_ball (half_lt_self hσ) hp.2)⟩
   obtain ⟨Q,hQ⟩:= ((hK.prod (isCompact_closedBall 0 (σ/2))).image (show Continuous Y from home n)).bddAbove_image (((panel_analytic L i X P B v hr).continuousOn.mono hc').norm)
   obtain ⟨a,h⟩:=observe L i X
   have hT:∀ᶠ y in (𝓝[fields n] (0:Points n)), y∈Z:= mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds (0:Points n) (half_pos hσ))
   have hP {x y:Points n}(hx:x∈k)(hz:y∈Z)(h:y∈ fields n): U (glow x y)=H (glow x y):= Eq.symm (panel_reached L i X P B v hr ⟨hc' (Set.mem_image_of_mem Y (Set.mk_mem_prod hx hz)),by simp[tube,h]⟩)
   haveI:=towards_shore (flat n)
   refine tendsto_nhds_unique (show Tendsto (fun y=> ∫ x,U (glow x y)*φ x) _ (𝓝 _) from cascade _ _ X a h φ hr) ?_
   apply tendsto_integral_filter_of_dominated_convergence (fun x=> Q*‖φ x‖)
   · filter_upwards [self_mem_nhdsWithin] with t ht using ((hU t ht).mul φ.continuous).aestronglyMeasurable
   · filter_upwards [self_mem_nhdsWithin,hT] with t ht hB
     filter_upwards with x; by_cases hh : φ x=0; · simp [hh]
     have he:x∈k:= subset_tsupport _ hh; rw [hP he hB ht,norm_mul]; exact mul_le_mul_of_nonneg_right (hQ (Set.mem_image_of_mem _ (Set.mem_image_of_mem Y (Set.mk_mem_prod he hB)))) (norm_nonneg _)
   · exact φ.integrable.norm.const_mul Q
   filter_upwards with x; by_cases he:φ x=0; · simp [he]
   have hα:=hp _ (subset_tsupport _ he);
   have hf:Tendsto (fun y=> H (glow x y)) (𝓝[fields n] (0:Points n)) (𝓝 (H (glow x 0))) := ((hα.continuousAt.comp ((home n).comp (continuous_const.prodMk continuous_id)).continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
   exact (hf.mul tendsto_const_nhds).congr' (((show ∀ᶠ y in (𝓝[fields n] 0), y∈fields n from self_mem_nhdsWithin).and hT).mono fun y hy=> congr_arg (·*(φ x)) (hP (subset_tsupport _ he) hy.2 hy.1).symm)

-- uniform power (derivative version via further compact enlargement later)
variable {L i} {hG:G.Simple}
omit hr in
lemma panel_growth (H:Roll.{u} F hG L) (v:∀ j:Fin n, ℝ→ S.Field (d j)) (hv:∀ j,Measured F (d j) (v j)) {K:Set (Full n)} (hk:IsCompact K) (hK:K⊆ P.zone):
    ∃ C:ℝ,0 ≤ C ∧ ∃ m:ℕ,∀ᶠ r in Trace.Pilot.trail,∀ (i:Survey F) (D:∀ n, Blanket n) (X:(Survey.reads L i).world.Aurora D),∀ z∈K, ‖panel L i X P B (fun j=>v j r) r z‖ ≤ C*Trace.Pilot.LogV r^m:=by
   obtain ⟨A,hA,m,h⟩:=Temperate.core H _ (fun i=> fly_measured H _ (B i) (hv i))
   let Q: Full n→L[ℂ] Full n:= reach P.g P.e P.speed
   obtain ⟨δ,h₁,h₂,h₃⟩:= ((Room.compact (hk.image Q.continuous) (Set.image_subset_iff.mpr (hK.trans (show P.zone ⊆ _ from P.fits)))).and ((show ∀ᶠ r in Trace.Pilot.trail, 0<r from self_mem_nhdsWithin).and ((ge_mem_nhds (show (0:ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds))).exists
   exact ⟨A*δ⁻¹^m,by positivity,m,h.mono fun r h i D X x hx=> (h.full i D X δ ⟨h₂,h₃⟩ (Q x) (h₁ _ (Set.mem_image_of_mem Q hx))).trans_eq (mul_right_comm ..)⟩
end YM.GapsContact.Jost
