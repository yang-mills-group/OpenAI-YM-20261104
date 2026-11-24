import YM.OPE.Compatible.Arch.Cred
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio
/-!
# EOM 1: Chart divergence from actual Haar, left and right.

No definition of the Haar score via a Jacobian
postulate. Compact-patch extraction gives all jets. Right uses
positive generator here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange
variable (R:LocalRatio P)
include R
lemma costsRight {f:G.Color→G.Color}{T:G.El≃ₜ G.El}(h:MeasurePreserving T G.probHaar G.probHaar){x:G.Color}
      (hx:x∈ball 0 P.radius) (hp:f x∈ball 0 P.radius)(hf:ContDiffAt ℝ ω f x)(hv:∀ᶠ y in 𝓝 x,G.lieExp (f y) = T (G.lieExp y)):
      P.J x=|(fderiv ℝ f x).det| * P.J (f x):=by
        let g(v:G.Color):=P.scale* P.J v; let D(v:G.Color):= |(fderiv ℝ f v).det| *g (f v)
        let s:= {v | v∈ball 0 P.radius ∧ f v∈ball 0 P.radius ∧ ContDiffAt ℝ ω f v ∧ G.lieExp (f v)=T (G.lieExp v)}
        have hs:s∈𝓝 x:= by filter_upwards [Metric.isOpen_ball.mem_nhds hx,hf.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hp),hf.eventually (by simp),hv] with v h₁ h₂ h₃ h₄ using ⟨h₁,h₂,h₃,h₄⟩
        have het:ContinuousAt D x:=by unfold D; refine ContinuousAt.mul (ContinuousAt.abs (ContinuousLinearMap.continuous_det.continuousAt.comp ((hf.fderiv_right (m:=ω) (by simp)).continuousAt))) ?_; exact ContinuousAt.comp (g:=g) (f:=f) (continuousAt_const.mul (R.germ _ hp).continuousAt) hf.continuousAt
        have h':ContinuousAt g x:= continuousAt_const.mul (R.germ _ hx).continuousAt; have hq:0≤g x:= (mul_pos R.scale (R.pos _ hx)).le
        have he(A:Set G.Color)(hA:IsCompact A)(hS:A⊆s): (∫⁻ x in A, ENNReal.ofReal (g x))=∫⁻ x in A, ENNReal.ofReal (D x):=by
          let B:= f '' A; have ht : ContinuousOn f A:=fun x hx=>(show ContDiffAt ℝ ω f _ from (hS hx).2.2.1).continuousAt.continuousWithinAt; have hb:= hA.image_of_continuousOn ht
          have hp : InjOn f A:= fun p h₁ q h₂ e=> R.inject ((hS h₁).1) ((hS h₂).1) (T.injective (((hS h₁).2.2.2).symm.trans ((congr_arg _ e).trans ((hS h₂).2.2.2))))
          have hu:T ⁻¹' (G.lieExp '' B)=G.lieExp '' A:=by rw [show G.lieExp '' B=T '' (G.lieExp '' A) from ?_, T.injective.preimage_image]; unfold B; rw [Set.image_image,Set.image_image]; exact Set.EqOn.image_eq fun i hi=>(hS hi).2.2.2
          unfold g; rw [← cap_price R A hA (by exact fun i hi=>(hS hi).1), ← hu, h.measure_preimage ((hb.image G.lieExp_cont).measurableSet.nullMeasurableSet), cap_price R B hb (by rintro _ ⟨x,hx,rfl⟩;exact (hS hx).2.1)]
          unfold D g; unfold B; rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA.measurableSet (f':=fun i=> fderiv ℝ f i) ?_ hp]; simp only [ENNReal.ofReal_mul (abs_nonneg _)]; exact fun i hi=> ((show ContDiffAt ℝ ω f i from (hS hi).2.2.1).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
        have hW:0≤ D x:=mul_nonneg (abs_nonneg _) (mul_pos R.scale (R.pos _ hp)).le
        have hH:= le_antisymm (price_le_of_caps hs het h' hW (fun t ht H=> (he t ht H).symm)) (price_le_of_caps hs h' het hq he); apply mul_left_cancel₀ R.scale.ne'; unfold D g at hH; rw [hH];ring
end YM.OPE.Variance
