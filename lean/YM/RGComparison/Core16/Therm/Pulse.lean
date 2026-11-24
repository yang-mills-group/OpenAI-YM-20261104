import YM.RGComparison.Core16.Therm.Brio
import YM.PhysicalNext.FLAT_PUSH_RESPONSE.OnTrack
import YM.Next.STATIONARY.Joint.Completion
/-!
# Supply the centered Wick work for f = testing the REAL germ
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Therm
open Function Filter MeasureTheory Set Metric Analysis
open PhysicalNext.FlatResponse
open scoped Topology ContDiff NNReal Matrix
open PertExtension PertExtension.Series Tested Radial
section general
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E]
   {f g : E → ℝ} {x : E} (u : E)
lemma score_two (f : E→ℝ) (x y : E) : score f x y 2 = iteratedFDeriv ℝ 2 f x ![y,y] / 2 := by
  unfold score Tensor.diagonal Tensor.coeff
  simp only [smul_apply,smul_eq_mul]
  rw [show (fun _ : Fin 2=> y) = ![y,y] from funext fun i=>by fin_cases i<;> rfl]; norm_num; ring
lemma score_one (f : E→ℝ) (x y : E) : score f x y 1= fderiv ℝ f x y := by
  simp [score,Tensor.diagonal,Tensor.coeff,iteratedFDeriv_one_apply]
lemma double (h : ContDiffAt ℝ ω f 0)(x : E)(he : ∀ t : ℝ, f (t • x)=f x*t^2) :
    jet f 1 x=0 ∧ jet f 2 x=f x := by
  have hx(k) : jet f k x= (k.factorial:ℝ)⁻¹ * iteratedDeriv k (fun t => f x*t^2) 0 := by
    rw [homogeneous_derivative _ _ _ (h.of_le le_top), show (fun t : ℝ=> f (t • x))=(fun t=> f x*t^2) from funext he]
  rw [hx,hx, iteratedDeriv_const_mul (hf:= (show ContDiffAt ℝ (↑(1:ℕ)) (fun t : ℝ=>t^2) 0 from contDiffAt_id.pow 2)), iteratedDeriv_const_mul (hf:= (show ContDiffAt ℝ (↑(2:ℕ)) (fun t : ℝ=>t^2) 0 from contDiffAt_id.pow 2)),iteratedDeriv_pow,iteratedDeriv_pow]; norm_num [Nat.descFactorial]; ring

lemma score_chassis {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]{f:X→ℝ}{F : E→X} {x : E} (hf : ContDiffAt ℝ ω f (F x)) (h : ContDiffAt ℝ ω F x) (he : fderiv ℝ f (F x)=0) : score (f ∘ F) x u 2=score f (F x) (fderiv ℝ F x u) 2 := by
  rw [score_two,YM.Stationary.pay_second hf h,he]; simp [score_two]
end general
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E]
      {f K : ℝ × E→ℝ} (v : ℝ)(x : E) (k : ℕ)

def pedal : ℝ×E→ℝ:= fun z=>z.1^2
def hub (f : ℝ × E → ℝ) : ℝ × E → ℝ := uncurry (spot f)

def clean (f : ℝ × E → ℝ) := pedal (E:=E)+hub f

def warmth (K : ℝ × E → ℝ) : ℝ × E → ℝ := fun v => K (v.1,0)

structure Coalescent (f : ℝ × E → ℝ) : Prop where
  smooth : ContDiffAt ℝ ω f 0
  backbone : ∀ᶠ x : ℝ in 𝓝 0, f (x,0) = x^2
  vertical : ∀ᶠ x : ℝ in 𝓝 0, fderiv ℝ (fun y:E=>f (x,y)) 0=0
  stable (v : E) (he : v ≠ 0) : 0 < jet (fun y:E=> f (0,y)) 2 v

lemma pedal_smooth : ContDiff ℝ ω (pedal (E:=E)) := contDiff_fst.pow 2
lemma hub_tick (f : ℝ × E → ℝ) (t : ℝ) : spot f v (t • x)=spot f v x * t^2 := by
  unfold spot; simp [map_smul]; ring
lemma spot_smooth (f : ℝ × E→ℝ) : ContDiff ℝ ω (spot f v) := by
  unfold spot; exact (((Bends f v).contDiff.clm_apply contDiff_id).div_const _)
lemma hub_birth (h : ContDiffAt ℝ ω f (v,0)) : ContDiffAt ℝ ω (hub f) (v,0) := by
  unfold hub spot; exact ((((Bends_diff h).comp (f:=Prod.fst) (v,(0:E)) contDiffAt_fst).clm_apply contDiffAt_snd).clm_apply contDiffAt_snd).div_const _
lemma pure_birth (h : ContDiffAt ℝ ω f (v,0)) : ContDiffAt ℝ ω (clean f) (v,0) := (pedal_smooth.contDiffAt).add (hub_birth v h)

lemma spot_three (f : ℝ×E→ℝ) : spot f v 0=0 ∧ jet (spot f v) 1 x=0 ∧ jet (spot f v) 2 x=spot f v x :=
   ⟨by simp [spot], double (spot_smooth v f).contDiffAt x (hub_tick v x f)⟩
lemma ticket (h : ContDiffAt ℝ ω f (v,0)) : score f (v,0) (0,x) k=jet (fun y=> f (v,y)) k x:= by
  rw [←score_jet]; let L : E→L[ℝ] ℝ × E:= ContinuousLinearMap.inr ℝ ℝ E; have hp := score_linear (k:=k) x L (v,0) (x:=0) (g:=f) (by rw [map_zero,add_zero]; exact h); rw [map_zero,add_zero] at hp; simpa only [L,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add] using hp.symm
lemma spot_eq (f : ℝ×E→ℝ) : spot f v x=jet (fun y=>f (v,y)) 2 x := by rw [←score_jet,score_two,iteratedFDeriv_two_apply]; rfl
lemma vert_smooth (h : ContDiffAt ℝ ω f (v,x)) : ContDiffAt ℝ ω (fun y=>f (v,y)) x:= h.comp x (contDiffAt_const.prodMk contDiffAt_id)
private lemma collected (h : ContDiffAt ℝ ω f 0) : ∀ᶠ v : ℝ in 𝓝 0, ContDiffAt ℝ ω f (v,0) :=
  ((continuous_id.prodMk (continuous_const (y:=(0:E)))).tendsto (0:ℝ)).eventually (h.eventually (by simp))

private lemma hub_low (h : ContDiffAt ℝ ω f 0) : Held (hub f) 2 x := by
  intro i hi; filter_upwards [collected h] with v hv
  have hb:= spot_three v x f; rw [ticket _ _ _ (hub_birth v hv)]; interval_cases i
  · exact (jet_zero ..|>.trans hb.1)
  exact hb.2.1

lemma split_prices (hf : ContDiffAt ℝ ω f 0) : jet (clean f) 1 (v,x)=0 ∧ jet (clean f) 2 (v,x)= v^2+spot f 0 x := by
  have hr : ContDiffAt ℝ ω (hub f) 0 := hub_birth 0 hf; have hp := pedal_smooth (E:=E).contDiffAt (x:=0)
  rw [clean,add_jet _ _ _ hp hr,add_jet _ _ _ hp hr]; have hh:= double hp (v,x) (by intro t; unfold pedal; simp; ring)
  rw [hh.1, hh.2, (hub_low x hf).each _ hr 1 (by decide), (hub_low x hf).at_lead _ hr]
  exact ⟨zero_add .., congr_arg (v^2+·) ( (ticket 0 x 2 hr).trans ((spot_three 0 x f).2.2))⟩

lemma pure_nil : clean f 0=0 := by change (0:ℝ)^2+spot f 0 0=0; rw [(spot_three 0 (0:E) f).1]; ring
namespace Coalescent
variable (h : Coalescent f)
include h
lemma margins (x : E) : Held (f-clean f) 3 x := by
  intro i hi; filter_upwards [h.backbone,h.vertical,collected h.smooth] with k hK hV hv
  rw [score_sub _ hv (pure_birth k hv), clean, score_add _ pedal_smooth.contDiffAt (hub_birth k hv), ticket _ _ _ hv,ticket _ _ _ pedal_smooth.contDiffAt, ticket _ _ _ (hub_birth k hv)]
  change jet _ i x - (jet (fun _ : E=>k^2) i x+jet (spot f k) i x)=0
  have hx (i) (e:i≠0) : jet (fun _ : E=>k^2) i x=0:= by simp [jet,iteratedFDeriv_const_of_ne e]
  interval_cases i
  · rw [jet_zero,jet_zero,jet_zero,hK,(spot_three k x f).1]; ring
  · rw [hx _ (by decide), (spot_three k x f).2.1,←score_jet,score_one,hV]; simp
  rw [hx _ (by decide),(spot_three k x f).2.2, spot_eq]; ring
lemma same (hk : k<3) : jet f k (v,x)=jet (clean f) k (v,x) := sub_eq_zero.mp ((sub_jet _ _ (v,x) h.smooth (pure_birth 0 h.smooth) k).symm.trans ((h.margins x).each _ (h.smooth.sub (pure_birth 0 h.smooth)) _ hk))

protected lemma candle (g : ContDiffAt ℝ ω K 0)(he : 0<K 0) [FiniteDimensional ℝ E] : Candle K (warmth K) f (clean f) := by
  have ht : ContDiffAt ℝ ω (clean f) 0:= pure_birth 0 h.smooth
  have hg : ContDiffAt ℝ ω (warmth K) 0 := g.comp (f:=fun x:ℝ×E=> (x.1,0)) 0 (contDiffAt_fst.prodMk contDiffAt_const)
  have hb := quadratic_min (clean f) (by
    rintro ⟨v,x⟩ hv
    rw [(split_prices v x h.smooth).2]
    by_cases hx:x=0
    · have hv' : v ≠ 0 := fun i=> hv (by rw [i,hx]; rfl); rw [hx,(spot_three 0 x f).1]; positivity
    exact add_pos_of_nonneg_of_pos (sq_nonneg v) ((spot_eq 0 x f)|>.symm ▸ h.stable x hx))
  constructor
  · exact ⟨⟨h.smooth.of_le le_top,h.backbone.self_of_nhds.trans (by norm_num),fun ⟨v,x⟩=> (h.same v x 1 (by decide)).trans (split_prices v x h.smooth).1⟩,⟨_,hb.choose_spec.1,fun ⟨v,x⟩=> (hb.choose_spec.2 (v,x)).trans_eq (h.same _ _ _ (by decide)).symm⟩,g,h.smooth,he⟩
  · exact ⟨⟨ht.of_le le_top,pure_nil,fun ⟨v,x⟩=> (split_prices v x h.smooth).1⟩, hb,hg,ht,he⟩
  · funext ⟨v,x⟩; change v^2+spot f v x=v^2+spot f v (-x); simp [spot]
  · rfl
  · intro v i hi; rw [show i=0 by omega]; exact Filter.Eventually.of_forall (fun x=> by simp [score_base,warmth])
  · exact h.margins
  intro x v; rw [(split_prices _ _ h.smooth).2,(split_prices _ _ h.smooth).2]; ring
end Coalescent

section tilt
variable (T : Secured f K){w : ℝ→E} (g : ContDiffAt ℝ ω w 0) (hw : HasFDerivAt w (0:ℝ →L[ℝ] E) 0) (hb : w 0=0)
include T g hw hb
lemma tilted_q : jet (f ∘ tilt w) 2 (v,x)=jet f 2 (v,x) ∧ Secured (f ∘ tilt w) (K ∘ tilt w) := by
  have hz : tilt w (0:ℝ×E)=0 := by change ((0:ℝ),w 0+(0:E))=0; rw [hb]; simp
  have hu : ContDiffAt ℝ ω (tilt w) 0 := contDiffAt_fst.prodMk ((g.comp (f:=Prod.fst) 0 contDiffAt_fst).add contDiffAt_snd)
  have ho : fderiv ℝ (tilt w) 0= ContinuousLinearMap.id ℝ (ℝ × E) := by
    have hi := (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt (x:=0); have he := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt (x:=0)
    have h : fderiv ℝ (tilt w) 0=_ := (hi.prodMk ((hw.comp 0 hi).add he)).fderiv
    rw [h]; ext x <;> simp
  have hh : ContDiffAt ℝ ω f (tilt w 0) := hz.symm ▸ T.paid.2.1
  have ht : fderiv ℝ f (tilt w 0)=0 := by
    rw [hz]; exact ContinuousLinearMap.ext (fun x=> ((score_one f 0 x).symm.trans (T.spread.base1 x)))
  have H(v x): jet (f ∘ tilt w) 2 (v,x)=jet f 2 (v,x):= by rw [←score_jet,score_chassis (v,x) hh hu ht,hz,ho]; rfl
  refine ⟨H v x,⟨(hh.comp _ hu).of_le le_top,(congr_arg f hz).trans T.spread.base0,fun x=>?_⟩, ⟨_,T.slope.choose_spec.1,fun ⟨v,x⟩=> (T.slope.choose_spec.2 (v,x)).trans_eq (H v x).symm⟩,(hz.symm ▸ T.paid.1 : ContDiffAt ℝ ω K (tilt w 0)).comp 0 hu,hh.comp 0 hu,(by rw [comp_apply,hz]; exact T.paid.2.2)⟩
  rw [←score_jet,score_one,fderiv_comp 0 (hh.differentiableAt (by simp)) (hu.differentiableAt (by simp)),ht]; simp
end tilt
end YM.RGComparison.Core16.Therm
