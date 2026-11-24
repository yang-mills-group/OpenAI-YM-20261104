import YM.RG17.Storage
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
obtain LogLaw (point contour in selected Final), not from a point PT value
but from matching smeared correlations on that measurement declaration,
plus phase costs paid by the same Final. Exact positive measure criterion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open Points Analysis Work.A05 Trace
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book} {F:Final C f S} {L:Layout F}

lemma offset_cont : Continuous separated:= (PiLp.continuous_toLp _ _).comp (continuous_pi (fun i=> by fin_cases i <;> [exact continuous_const; exact continuous_id.smul continuous_const]))
lemma offsetConf {r:ℝ}(hr:0<r): separated r∈ conf _:=Trace.room_conf _ _ _ _ _ (room_separated r hr.le) hr one_pos
lemma span_sep {r:ℝ}(hr:0<r):span2 (separated r)=r:=by change ‖r • basis timeAxis-0‖ = r; rw [sub_zero,norm_smul, Real.norm_of_nonneg hr.le,basis_norm,mul_one]
-- unselected evaluation moved to rest, and from there to selected one
-- for positivity. Costs proportional to profile.
def selectedW (F:Final C f S)(r:ℝ) (x:Points 2) := discount r • restTrace F (meanExact F) (r*span2 x)
def pulse (F:Final C f S)(r:ℝ)(t:ℝ) := discount r * (restTrace F (meanExact F) (r*t)).re

lemma actualReal (F:Final C f S){r:ℝ}(hr:0<r){x:Points 2}(hx:x∈ conf 2) : selectedW F r x=↑(pulse F r (span2 x)):=by
   obtain ⟨M,H,hM,he,-⟩:= centered_spectral F
   unfold selectedW pulse; rw [he _ (mul_pos hr (spanPos hx)),Complex.real_smul]; norm_num
lemma rest_real (F:Final C f S){r s:ℝ} (hr:0<r)(hs:0<s): discount r • restTrace F (meanExact F) (r*s)=↑(pulse F r s):=by
    have h:= actualReal F hr (offsetConf hs); unfold selectedW at h; rw [span_sep hs] at h; exact h
lemma pulse_le (F:Final C f S){r s t:ℝ}(hr:0<r)(hs:0<s)(h:s ≤ t): pulse F r t ≤ pulse F r s:=by
   obtain ⟨M,H,hM,he,-⟩:= centered_spectral F
   have hh:=mul_pos hr hs;have ht:=mul_pos hr (hs.trans_le h)
   unfold pulse; rw [he _ ht, he _ hh]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hr.le _) (sq_nonneg _))
   refine (show (∫ p:E4,Real.exp (-(r*t)*time p) ∂M) ≤ ∫ p:E4,Real.exp (-(r*s)*time p) ∂M from MeasureTheory.integral_mono_ae (H.integrable_exp M hM ht) (H.integrable_exp M hM hh) ?_ )
   filter_upwards [(show ∀ᵐ p:E4 ∂M,p∈Mink.cone from ae_iff.mpr hM)] with x hx using Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg (mul_le_mul_of_nonneg_left h hr.le)) ((Mink.cone_self x).mp hx).1)
lemma selected_cont (F:Final C f S){r:ℝ}(hr:0<r): ContinuousOn (selectedW F r) (conf 2) :=by
    let K:= F.α.ensemble F.α.atPoint
    have hh: K.Hierarchy:= spectate F (some F.α.atPoint)
    let Z:=fun x=> separated (r*span2 x)
    change ContinuousOn (fun x:Points 2=> discount r • S.useAt K (Z x) _) _
    exact (continuousOn_const (c:=discount r)).smul ((S.class_smooth K hh.smooth _).continuousOn.comp (offset_cont.comp (continuous_const.mul span_cont)).continuousOn (fun _ hx=> offsetConf (mul_pos hr (spanPos hx))))
lemma regionReal {B:Points 2→ℝ}(ht: ContinuousOn B (conf 2)) (ψ:RealTest 2): Integrable (fun x=> ψ x * B x) := by
    let ψ':Test 2:= ⟨Complex.ofRealCLM ∘ ψ,Complex.ofRealCLM.contDiff.comp ψ.contDiff, ψ.hasCompactSupport.comp_left (g:=Complex.ofReal) (by simp), (tsupport_comp_subset (g:=Complex.ofReal) (by simp) _).trans ψ.tsupport_subset⟩
    have hm:= Complex.reCLM.integrable_comp (ψ'.smearing (Complex.continuous_ofReal.comp_continuousOn ht))
    apply hm.congr (Eventually.of_forall (fun x=>?_))
    change ((ψ x:ℂ)*(B x:ℂ)).re=_; rw [← Complex.ofReal_mul];rfl
lemma actualInt (F:Final C f S){r:ℝ}(hr:0<r)(ψ:RealTest 2): Integrable (fun x=> ψ x * pulse F r (span2 x)) := by
    have ht: ContinuousOn (fun x=> pulse F r (span2 x)) (conf 2):= (Complex.continuous_re.comp_continuousOn (selected_cont F hr)).congr (fun x hx=> by simp [Function.comp_apply, actualReal F hr hx])
    exact regionReal ht ψ

lemma spanned (F:Final C f S) (H:Services C f S) (ψ:Test 2) : Tendsto (fun r=> ψ.applyTo (selectedW F r)-ψ.applyTo (fun y=> discount r • θDiagram F (r•y))) home (𝓝 0):=by
    let J : Points 2→ Points 2:= separated ∘ span2
    let K:= J '' tsupport ψ; obtain ⟨A,e,hA,he,hK⟩:=roomCosts (K:=K) (ψ.hasCompactSupport.image (offset_cont.comp span_cont)) (image_subset_iff.mpr (fun i hi=> offsetConf (spanPos (ψ.tsupport_subset hi))))
    let v (r:ℝ) (x:Points 2):= selectedW F r x-discount r • θDiagram F (r•x)
    have hφ {r:ℝ} (hr:0<r) :ContinuousOn (fun x:Points 2=> discount r • θDiagram F (r•x)) (conf 2):= (continuousOn_const (c:=discount r)).smul ((toward_contrary F).comp (show Continuous (fun x:Points 2=> r•x) by fun_prop).continuousOn (fun _ hx=> smul_conf hr hx))
    have hx {r:ℝ} (hr:0<r) : ψ.applyTo (selectedW F r)-ψ.applyTo (fun y=> discount r • θDiagram F (r•y))=ψ.applyTo (v r):=by
       unfold Test.applyTo; rw [← integral_sub (ψ.smearing (selected_cont F hr)) (ψ.smearing (hφ hr))]; exact integral_congr_ae (Eventually.of_forall (fun y=>(mul_sub ..).symm))
    apply Tendsto.congr' (f₁:=fun r=> ψ.applyTo (v r)) (positiveLength.mono fun r hr=>(hx hr).symm)
    let u:=∫ x, ‖ψ x‖; have hu:0≤u:=integral_nonneg fun _=>norm_nonneg _
    apply Metric.tendsto_nhds.mpr; intro ε hε; let c:= ε/(u+1); have hc:0<c:=by unfold c; positivity
    filter_upwards [positiveLength,Trace.log_agreement F H A e c hc hA he] with r hr hV
    rw [dist_zero_right]; refine (test_doms ψ _ c (fun x hx=>?_)).trans_lt (by change u*c<ε; unfold c; field_simp;simp) -- fix
    have hz: x∈conf _:=ψ.tsupport_subset hx
    have hw : points (posed r (J x))=separated (r * span2 x):= unit_test r (span2 x)
    unfold v selectedW; rw [← smul_sub, restTrace_origin,θ_norm_rep F _ (smul_conf hr hz)]
    rw [show ‖(r•x) 1-(r•x) 0‖ = _ from span_sc x hr, discount, OPE.run, ←Real.log_inv, ← hw]
    exact (hV _ 0 (hK _ hr _ (Set.mem_image_of_mem _ hx)) (some F.α.atPoint) none).le

abbrev asComplex (ψ:RealTest 2): Test 2:=⟨Complex.ofRealCLM ∘ ψ, Complex.ofRealCLM.contDiff.comp ψ.contDiff, ψ.hasCompactSupport.comp_left (g:=Complex.ofReal) (by simp), (tsupport_comp_subset (g:=Complex.ofReal) (by simp) _).trans ψ.tsupport_subset⟩

lemma spectrum_test {B:Points 2→ℂ}{g:Points 2→ℝ}(h:EqOn B (Complex.ofReal ∘ g) (conf 2))(ψ:RealTest 2) :
   (asComplex ψ).applyTo B = Complex.ofReal (∫ x:Points 2,ψ x*g x):=by rw [(asComplex ψ).apply_eq h, ← integral_complex_ofReal]; apply integral_congr_ae; filter_upwards with x; exact (Complex.ofReal_mul ..).symm
lemma attested (F:Final C f S){r:ℝ}(hr:0<r)(ψ:RealTest 2) :
   (asComplex ψ).applyTo (selectedW F r) = Complex.ofReal (∫ x:Points 2,ψ x*pulse F r (span2 x)) := spectrum_test (fun x hx=> actualReal F hr hx) ψ
lemma free_cont (C:Family G) : ContinuousOn (fun x=>freeCharge C (span2 x)) (conf 2):= continuousOn_const.div (span_cont.pow 8).continuousOn (fun _ hx=>pow_ne_zero _ (spanPos hx).ne')
variable (Z:Ledger L)(A:Ports C)(H:Services C f S) (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (loc:Located L)(V:Tide Z A)(Q:Passage Z A)(t:Handles L)
include Z A H P loc V Q t
lemma alongRealm (ψ:RealTest 2): Tendsto (fun r=> ∫ x:Points 2,ψ x*pulse F r (span2 x)) home (𝓝 (∫ x:Points 2,ψ x*freeCharge C (span2 x))) := by
   have he:= (spanned F H (asComplex ψ)).add (accumulated Z A H P loc V Q t (asComplex ψ)); rw [zero_add] at he
   have hp:Tendsto (fun r=> (asComplex ψ).applyTo (selectedW F r)) home (𝓝 (Complex.ofReal (∫ x:Points 2,ψ x*freeCharge C (span2 x)))):= by
      rw [← spectrum_test (B:=modCharge C) (g:=fun x=> freeCharge C (span2 x)) (fun _ _=> rfl)]
      exact he.congr (fun r=> sub_add_cancel ..)
   refine (Complex.continuous_re.continuousAt.tendsto.comp hp).congr' (positiveLength.mono (fun r hr=> ?_))
   dsimp only [Function.comp_apply]; rw [attested F hr];rfl
end YM.RG17
