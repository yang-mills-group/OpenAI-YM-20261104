import YM.OPE.Compatible.Navy.Tank
/-!
# Exponential seams arbitrary stands for exact smooth germ inputs
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Pilot
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{I J V D:Type}[Fintype I][Fintype J]
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
local notation "X" => Keys G I
section
variable (A:Dimes G I J) (B:Dimes G J I)(hp:B.q=A.q.symm)
lemma outing : ∀ᶠ x:Keys G I in 𝓝 0, put (A.gradient x)= A.q (put x):=by
      let F:X→ Tile G J:= A.q∘ put; have hh:Tendsto F (𝓝 0) (𝓝 1):=by simpa only [Function.comp_apply,put_zero,A.clan] using (A.q.continuous.comp putC).tendsto 0
      filter_upwards [A.lead_grad,hh.eventually Stand.sphere] with i hi hg; rw [hi];exact hg
include hp
lemma coil : B.gradient ∘ A.gradient=ᶠ[𝓝 0] id :=by
     filter_upwards [outing A, (show Tendsto A.gradient (𝓝 0) (𝓝 0) from A.grad0 ▸ A.gradC.continuousAt.tendsto).eventually (outing B),local_intro (G:=G) (I:=I),((show Tendsto B.gradient (𝓝 0) (𝓝 0) from B.grad0 ▸ B.gradC.continuousAt.tendsto).comp (show Tendsto A.gradient (𝓝 0) (𝓝 0) from A.grad0 ▸ A.gradC.continuousAt.tendsto)).eventually (local_intro (G:=G) (I:=I))] with i hi hv hz hx; change intake _ _ (put (B.gradient _))= B.gradient (A.gradient i) at hx; change B.gradient _=i; rw [←hx,hv,hi,hp,A.q.symm_apply_apply,hz]
lemma empty_coil (L:Lid G J): Cel (L.f∘A.gradient):=by
      apply Radial.quadratic_min; intro x hx; let M:=fderiv ℝ A.gradient 0; have h: Function.Injective M:=by
           have he:fderiv ℝ B.gradient 0∘L M=1:=by
              have hv:=coil A B hp; have hh : fderiv ℝ (B.gradient ∘ A.gradient) 0=1:=hv.fderiv_eq.trans (fderiv_id ..); rw [fderiv_comp, A.grad0] at hh; exact hh; · rw [A.grad0];exact B.gradC.differentiableAt (by simp)
              exact A.gradC.differentiableAt (by simp)
           intro i j e; have hp(i:X): fderiv ℝ B.gradient 0 (M i)=i:=DFunLike.congr_fun he i; rw [← hp i,e, hp]
      have hu:jet (L.f∘ A.gradient) 2 x=jet L.f 2 (M x):=by unfold jet; rw [slopeJet A.gradient A.gradC A.grad0 _ L.F]; rfl
      rw [hu]; obtain ⟨c,hc,ht⟩:=L.bright; exact (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr (show M x≠0 from fun e=>hx (h (e.trans (map_zero M).symm)))))).trans_le (ht _)
lemma newLid (L:Lid G J){f w:Keys G I→ℝ}(h:Measurable f)(hk:Measurable w)(he:f=ᶠ[𝓝 0] L.f ∘ A.gradient)(hw:w=ᶠ[𝓝 0] L.w∘A.gradient):∃ R:Lid G I,R.f=f∧R.w=w:=by
      let p:=L.f ∘ A.gradient
      have hu:= A.chore L
      have hh x n : jet f n x= jet p n x:=by unfold jet; rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
      refine ⟨⟨f,⟨hu.smooth.congr_of_eventuallyEq he, he.eq_of_nhds.trans hu.base0,fun i=> (hh i 1).trans (hu.base1 i)⟩,h, ?_,w,?_,?_,hk⟩,rfl,rfl⟩
      · obtain ⟨c,hc,h⟩:= empty_coil A B hp L; exact ⟨c,hc,fun x=>(hh x 2).symm ▸ h x⟩
      · rw [hw.eq_of_nhds,_root_.Function.comp_apply,A.grad0]; exact L.charm
      exact ((show ContDiffAt ℝ ∞ L.w (A.gradient 0) from A.grad0.symm ▸ L.coat).comp _ A.gradC).congr_of_eventuallyEq hw
end
end YM.OPE.Cascade.Pilot
