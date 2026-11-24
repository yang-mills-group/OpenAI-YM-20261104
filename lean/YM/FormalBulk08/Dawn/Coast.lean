import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.Normed.Module.HahnBanach
import YM.FormalBulk08.Dawn.Parchment

/-!
Dual of Panel actually yields BV measures, enough for existential packet
renderings. No invocation of compact-open Taylor interpolation, no closure
of arbitrary support. Positive decomposition via affine two copies. Real
polarities, explicit for external independent derivative stubs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Dawn
open Filter Set MeasureTheory CompactlySupported Function
open scoped BigOperators Topology ENNReal Classical
abbrev Hub := C(Pier,ℝ)
abbrev Mirror := Hub × Hub

def vise : ℝ× Hub →ₗ[ℝ] Mirror where
   toFun p:= (ContinuousMap.const Pier p.1 + p.2, ContinuousMap.const Pier p.1-p.2)
   map_add' := by rintro ⟨a,b⟩ ⟨c,d⟩; ext <;> simp <;> ring
   map_smul' := by rintro a ⟨b,c⟩; ext p <;> simp
                   ring
@[simp] lemma vise_zero (f : Hub) : vise (0,f)=(f,-f):=by simp [vise]
lemma vise_price (a : ℝ)(f : Hub) : ‖a‖+‖f‖≤‖vise (a,f)‖ := by
   let p:=vise (a,f)
   suffices h: ‖f‖≤‖p‖-‖a‖ from (le_sub_iff_add_le'.mp h)
   have hv x : ‖f x‖≤‖p‖-‖a‖ := by
      rw [le_sub_iff_add_le']
      have h : ‖a + f x‖≤ ‖p‖:= (p.1.norm_coe_le_norm x).trans (le_max_left ..)
      have he : ‖a - f x‖≤‖p‖:= (p.2.norm_coe_le_norm x).trans (le_max_right ..)
      simp_rw [Real.norm_eq_abs,abs_le] at h he
      rw [Real.norm_eq_abs,Real.norm_eq_abs]; rcases le_total 0 a with ha|ha <;> rcases le_total 0 (f x) with hf|hf <;> first| (rw [abs_of_nonneg ha, abs_of_nonneg hf]; linarith) | (rw [abs_of_nonneg ha,abs_of_nonpos hf];linarith)|(rw [abs_of_nonpos ha,abs_of_nonneg hf];linarith)|(rw [abs_of_nonpos ha,abs_of_nonpos hf];linarith)
   exact (ContinuousMap.norm_le _ ((norm_nonneg _).trans (hv origin))).mpr hv
lemma vise_inj : Injective vise:= (LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr (by
   rintro ⟨a,b⟩ (h : vise _=0)
   have he:=vise_price a b;rw [h,norm_zero] at he
   have ha : a=0:=norm_le_zero_iff.mp (by linarith [norm_nonneg b]); rw [ha,norm_zero,zero_add] at he; rw [ha,norm_le_zero_iff.mp he]; rfl)))

lemma offsets {X:Type*} [NormedAddCommGroup X][NormedSpace ℝ X](p:Submodule ℝ X)(g:p →ₗ[ℝ]ℝ)(C:ℝ)(hp:0≤C)(h:∀ x,‖g x‖≤C*‖x‖):∃ F:X→L[ℝ]ℝ,(∀ x : p,F x=g x) ∧ ‖F‖≤C := by
   let G:= LinearMap.mkContinuous g C h
   obtain ⟨F,hF,hσ⟩:= exists_extension_norm_eq p G; exact ⟨F,hF,hσ.le.trans (G.opNorm_le_bound hp h)⟩
set_option maxHeartbeats 600000 in
lemma polarize (b : Hub→L[ℝ]ℝ): ∃ L:Mirror →L[ℝ]ℝ, ‖L‖≤‖b‖ ∧ ∀ α g,L (vise (α,g))= ‖b‖*α+b g := by
   let f : ℝ×Hub→L[ℝ]ℝ := ‖b‖ • ContinuousLinearMap.fst ℝ ℝ Hub + b ∘L ContinuousLinearMap.snd ℝ ℝ Hub
   let e:=LinearEquiv.ofInjective vise vise_inj
   let g := f.toLinearMap ∘ₗ e.symm.toLinearMap
   have h (α p): g (e (α,p))=‖b‖*α+b p:=by simp [f,g]
   have he (x : vise.range): ‖g x‖≤‖b‖*‖x‖:= by
      obtain ⟨⟨a,p⟩,rfl⟩:= e.surjective x
      rw [h]
      refine (norm_add_le ..).trans ?_; rw [_root_.norm_mul,Real.norm_of_nonneg (norm_nonneg b)]
      exact (add_le_add_right (b.le_opNorm _) _).trans ((mul_add ..).ge.trans (mul_le_mul_of_nonneg_left (vise_price a p) (norm_nonneg _))) -- naming
   obtain ⟨F,hF,hG⟩:=offsets vise.range g ‖b‖ (norm_nonneg b) he
   refine ⟨F,hG,fun a p=>?_⟩
   exact (hF (e (a,p))).trans (h a p)

private lemma capceeds (f : Hub)(hf : 0≤f)(q : ℝ)(h:‖f‖≤q) : ‖ContinuousMap.const Pier q-f‖ ≤ q := by
   refine (ContinuousMap.norm_le _ ((norm_nonneg _).trans h)).mpr fun x=>?_
   have h : ‖f x‖≤q := (f.norm_coe_le_norm x).trans h
   change ‖q - f x‖≤q; rw [Real.norm_eq_abs] at h ⊢; have he : 0≤ f x:=hf x; rw [abs_of_nonneg he] at h; rw [abs_of_nonneg (sub_nonneg.mpr h)]; exact sub_le_self _ he
set_option maxHeartbeats 600000 in
lemma positive_view {L : Mirror→L[ℝ]ℝ} (Z:ℝ)(h:‖L‖≤Z) (he : L (vise (1,0))=Z) : Monotone L := by
   intro p q ht; let a:=q-p;have hA : 0 ≤ a:=sub_nonneg.mpr ht;rw [←sub_nonneg,←map_sub]
   let r:=‖a‖; let u:= vise (1,0)
   have he' f : f • u=(ContinuousMap.const Pier f,ContinuousMap.const Pier f) := by ext <;> simp [u,vise]
   have hw : ‖r • u - a‖≤ r := by rw [he',Prod.norm_def]; exact max_le (capceeds a.1 hA.1 _ (le_max_left ..)) (capceeds a.2 hA.2 _ (le_max_right ..))
   have ht : ‖L (r • u-a)‖ ≤ Z*r:= (L.le_opNorm _).trans (mul_le_mul h hw (norm_nonneg _) ((norm_nonneg L).trans h))
   rw [map_sub,map_smul,he,smul_eq_mul,Real.norm_eq_abs,abs_le] at ht
   change 0≤L a; nlinarith

lemma measure_ball (b:Hub→L[ℝ]ℝ)(h:Monotone b) : ∃ μ:Measure Pier, IsFiniteMeasure μ ∧ ∀ x:Hub,b x=∫ t,x t ∂μ := by
   let L:C_c(Pier, ℝ) →ₚ[ℝ] ℝ := {
      toFun := fun f=> b f.1
      map_add' := fun f g=> b.map_add _ _
      map_smul' := fun i p=> b.map_smul _ _
      monotone' := fun f g he=> h he
   }
   exact ⟨RealRMK.rieszMeasure L,inferInstance,fun f=> (RealRMK.integral_rieszMeasure L ⟨f,HasCompactSupport.of_compactSpace _⟩).symm⟩

/-- Two genuine measures, pay for evaluations of both. -/
lemma dual_ferns (b:Hub→L[ℝ]ℝ) : ∃ μ ν:Measure Pier, IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ μ.real univ + ν.real univ= ‖b‖ ∧ ∀ x:Hub, b x= (∫ t, x t ∂μ) - ∫ t,x t ∂ν := by
    obtain ⟨L,h,hL⟩:=polarize b
    have he : L (vise (1,0))=‖b‖:=by rw [hL,map_zero,mul_one,add_zero]
    have H:=positive_view _ h he
    obtain ⟨μ,hμ,hp⟩ := measure_ball (L ∘L ContinuousLinearMap.inl ℝ _ _) (fun _ _ ht=> H (show (_, (0:Hub))≤(_, 0) from ⟨ht,le_rfl⟩))
    obtain ⟨ν,hν,hq⟩:= measure_ball (L ∘L ContinuousLinearMap.inr ℝ _ _) (fun _ _ ht=> H (show ((0:Hub),_)≤(0,_) from ⟨le_rfl,ht⟩))
    refine ⟨μ,ν,hμ,hν,?_,fun x=>?_⟩
    · have hv : vise (1,0)=(1,0)+(0,1):=by ext <;> simp [vise]
      rw [hv,map_add,show L (1,0)=_ from hp 1,show L (0,1)=_ from hq 1] at he; simpa using he
    have hx := hL 0 x; rw [mul_zero,zero_add,vise_zero,show (x,-x)=(x,0)-(0,x) by simp,map_sub] at hx; exact hx.symm.trans (congr_arg₂ (·-·) (hp x) (hq x))
end YM.FormalBulk08.Dawn
