import YM.OPE.Compatible.Straws.Wan
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Fiber
open Stranded Shift Glass Score
variable {J V:Type}[Fintype J][Fintype V]
local notation "UT"=> Tile G D
local notation "YT"=> Tile G I
local notation "Δ"=> Equiv.refl (D⊕I)
local notation "Θ"=> shoot Δ G.El
attribute [local instance] Gauge.frobInner
lemma spar (Y:Score I V)(g:Keys G D→ Tile G V)(h: ∀ i,ContDiffAt ℝ ∞ (fun x=> G.mat (g x i)) 0) (he:Y.dress (g 0) 1=1): ∃ Ω:Dimes G (D⊕I) (D⊕I),∀ᶠ x in 𝓝 (0:Keys G (D⊕I)), BL (Ω.gradient x)= BL x ∧ put (BR (Ω.gradient x))= Y.dress (g (BL x)) (put (BR x)):=by
        obtain ⟨s,hs,hx⟩:=perch g h; let F: UT×YT→UT×YT:= fun i=>(i.1,Y.dress (s i.1) i.2); let A:(UT×YT)≃ₜ (UT×YT):=
            { toFun:=F
              invFun:=fun j=>(j.1,Y.dress (s j.1)⁻¹ j.2)
              left_inv := fun x=>by dsimp only [F]; rw [Y.dandy,inv_mul_cancel,Y.dance]
              right_inv := fun x=>by dsimp only [F]; rw [Y.dandy,mul_inv_cancel,Y.dance]
              continuous_toFun := continuous_fst.prodMk (continuous_pi fun i=> by unfold Score.dress;fun_prop)
              continuous_invFun:= continuous_fst.prodMk (continuous_pi fun i=> by unfold Score.dress;fun_prop) }
        let q:= (Θ).trans (A.trans (Θ).symm); have hW(x) : Θ (q x)=F (Θ x):=by unfold q; simp only [Homeomorph.trans_apply,Homeomorph.apply_symm_apply]; rfl
        have hR:q 1=1:=by
           apply (Θ).injective; rw [hW (1:_),show Θ 1= ((1:UT),(1:YT)) from rfl]
           have hv : s 1=g 0:= (by rw [←(show s ∘ put=ᶠ[𝓝 0] g from hx).eq_of_nhds,Function.comp_apply,put_zero]); change ((1:UT),Y.dress (s 1) 1)=(1,1); rw [hv,he]
        have H : ∀ᶠ x in 𝓝 (0:Keys G (D⊕I)), Θ (q (put x))= (put (BL x),Y.dress (g (BL x)) (put (BR x))):=by
           filter_upwards [((show Tendsto BL (𝓝 0) (𝓝 0) from (BL).map_zero ▸ (BL).continuous.continuousAt.tendsto)).eventually hx] with i hi; rw [hW]; change (put (BL i),Y.dress (s (put (BL i))) (put (BR i)))= _; rw [hi]
        have hp : ContDiffAt ℝ ∞ (fun x:K!=> unput (q (put x))) 0:=by
          apply contDiffAt_pi.mpr; intro i; have hl: ContDiffAt ℝ ∞ G.plog (G.mat (q (put (0:K!)) i)):=by rw [put_zero,hR]; exact G.plog_diff.of_le le_top
          apply hl.comp (f:=fun x:K!=> G.mat (q (put x) i)) 0; cases i with
          | inl y=> exact ((Stand.paintD (0:K!) _).of_le le_top).congr_of_eventuallyEq (H.mono fun i hi=>congr_arg G.mat (show q (put i) (.inl y)=put i (Sum.inl y) from congr_fun (congr_arg Prod.fst hi) y)) -- 
          | inr y=>
             suffices hp : ContDiffAt ℝ ∞ (fun x:K!=> G.mat (Y.dress (g (BL x)) (put (BR x)) y)) 0 from hp.congr_of_eventuallyEq (H.mono fun i hi=>congr_arg G.mat (show q (put i) (.inr y)= _ from congr_fun (congr_arg Prod.snd hi) y))
             have ht(y:V): ContDiffAt ℝ ∞ (fun x:K!=> G.mat (g (BL x) y)) 0:= ((show ContDiffAt ℝ ∞ _ ((BL) 0) from (BL).map_zero.symm ▸ h y)).comp (g:=fun x=> G.mat (g x y)) _ (BL).contDiff.contDiffAt
             unfold Score.dress; simp only [G.mat_mul,G.mat_inv]; exact ((ht _).mul ((Stand.paintD ..).of_le le_top)).mul ((starL' ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ (ht _)) -- infer
        let B:= Gem G D; let μ:=Gem G (D⊕I); let ν:=Gem G I
        have heo:MeasurePreserving Θ μ (B.prod ν):=by
             refine ⟨(Θ).measurable,?_⟩; have he: μ= Measure.map (Θ).symm (B.prod ν):=(brewing Δ G).map_eq.symm; rw [he,Measure.map_map (Θ).measurable (Θ).symm.measurable, show ⇑(Θ) ∘ (Θ).symm=_root_.id from funext fun i=> (Θ).apply_symm_apply i,Measure.map_id]
        have hU:MeasurePreserving q μ μ:=by
             have ht:MeasurePreserving A (B.prod ν) (B.prod ν):=by
                  have hb(x:UT):MeasurePreserving (Y.dress (s x)) ν ν:= measurePreserving_pi _ _ fun i=> (measurePreserving_mul_right _ _).comp (measurePreserving_mul_left _ _)
                  refine ⟨A.measurable,?_⟩; ext d hd; rw [Measure.map_apply A.measurable hd,Measure.prod_apply (A.measurable hd), Measure.prod_apply hd]; exact lintegral_congr_ae (Eventually.of_forall fun i=> (hb i).measure_preimage (s:=(Prod.mk i) ⁻¹' d) ((hd.preimage (measurable_const.prodMk measurable_id)).nullMeasurableSet))
             exact ((brewing Δ G).comp ht).comp heo
        let Ω:Dimes G (D⊕I) (D⊕I):=⟨q,hU,hR,hp⟩; have ht: Tendsto (Ω.gradient) (𝓝 0) (𝓝 0):= by simpa only [Ω.grad0] using Ω.gradC.continuousAt.tendsto
        have hh: Tendsto (fun x:K!=> q (put x)) (𝓝 0) (𝓝 1):=by simpa only [Function.comp_apply,put_zero,hR] using! (q.continuous.comp putC).tendsto (0:K!)
        refine ⟨Ω,?_⟩; have hb:Tendsto BL (𝓝 0) (𝓝 0):=(BL).map_zero ▸ (BL).continuous.continuousAt.tendsto
        filter_upwards [Ω.lead_grad,H, hh.eventually Stand.sphere, hb.eventually local_zone,(hb.comp ht).eventually local_zone] with i hi hy hk hh' hq
        have hw : put (Ω.gradient i)=q (put i):=by rw [hi];exact hk
        rw [←hw] at hy; obtain ⟨he,hp⟩:= Prod.mk.inj (show (put (BL (Ω.gradient i)),put (BR (Ω.gradient i)))= _ from hy); simp only [Function.comp_apply,he,hh'] at hq; exact ⟨hq.symm,hp⟩
end Fiber
end YM.OPE.Libra
