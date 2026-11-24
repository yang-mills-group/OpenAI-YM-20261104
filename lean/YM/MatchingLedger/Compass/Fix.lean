import YM.LocalH.Haar
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Charts compared with authoritative exponential-coordinate normalization

In any scheme consuming the same group. Both the density entering any germ jets
and the scale read at zero. No claim about extending outside approved ball.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Compass
open Function Filter Set MeasureTheory Metric RG Precision
open scoped ContDiff BigOperators Topology Matrix.Norms.Frobenius ENNReal Classical
variable {G:Gauge} {C:ChartRatio G} (h:LocalRatio C)

namespace Interiors
include h
private def mass (C:ChartRatio G)(x:G.Color):= ENNReal.ofReal (C.scale*C.J x)
lemma forum {S : Set G.Color} (hp:S⊆ball 0 C.radius)(hq:MeasurableSet S):
    (∫⁻ x in S, mass C x)= G.probHaar (G.lieExp '' S):=by
  have he := G.lieExp_cont.measurable
  let Z:=G.lieExp '' S
  have hx : MeasurableSet Z:= hq.image_of_continuousOn_injOn G.lieExp_cont.continuousOn (InjOn.mono hp h.inject)
  have hy : Z⊆ G.lieExp '' ball 0 C.radius:= image_mono hp
  have hv := congr_arg (fun M : Measure G.El=> M Z) h.actual
  change Measure.map G.lieExp _ Z=(G.probHaar.restrict _) Z at hv
  rw [Measure.restrict_apply hx, inter_eq_left.mpr hy, Measure.map_apply he hx, withDensity_apply _ (he hx),Measure.restrict_restrict (he hx)] at hv
  rw [show G.lieExp ⁻¹' Z ∩ ball (0:G.Color) C.radius=S from ?_] at hv; exact hv
  ext i; constructor
  · rintro ⟨⟨j,hj,hJ⟩,hS⟩
    exact (h.inject (hp hj) hS hJ) ▸ hj
  intro hi; exact ⟨⟨i,hi,rfl⟩,hp hi⟩
lemma shared {D:ChartRatio G}(ht:LocalRatio D) :
     C.scale=D.scale ∧ EqOn C.J D.J (ball 0 (min C.radius D.radius)):=by
   let r:= min C.radius D.radius; let T:= ball (0:G.Color) r
   have hr : 0<r:= lt_min h.patch ht.patch
   have hp : T⊆ball 0 C.radius:= ball_subset_ball (min_le_left ..)
   have hq : T⊆ball 0 D.radius:= ball_subset_ball (min_le_right ..)
   let V:=volume.restrict T; have hV : SigmaFinite V := by unfold V; infer_instance
   have he : mass C =ᵐ[V] mass D:= by
      have hf(X:ChartRatio G)(he:LocalRatio X): AEMeasurable (mass X) V:= (Measurable.ennreal_ofReal (by exact (measurable_const.mul he.borel))).aemeasurable
      apply (withDensity_eq_iff_of_sigmaFinite (hf C h) (hf D ht)).mp
      ext S hS
      rw [withDensity_apply _ hS,withDensity_apply _ hS]; unfold V; rw [Measure.restrict_restrict hS]; exact (forum h (inter_subset_right.trans hp) (hS.inter Metric.isOpen_ball.measurableSet)).trans (forum ht (inter_subset_right.trans hq) (hS.inter Metric.isOpen_ball.measurableSet)).symm
   have hv(X:ChartRatio G)(he:LocalRatio X) : ContinuousOn (mass X) (ball 0 X.radius):= (ENNReal.continuous_ofReal.continuousOn.comp (t:=Set.univ) (continuousOn_const.mul (fun x hx=>(he.germ x hx).continuousAt.continuousWithinAt)) (mapsTo_univ ..))
   have hy(x)(hx:x∈T) := congr_arg ENNReal.toReal (Measure.eqOn_of_ae_eq he ((hv _ h).mono hp) ((hv _ ht).mono hq) (by rw [show interior T=T from isOpen_ball.interior_eq]; exact subset_closure) hx)
   have hx (x)(hh:x∈T): C.scale*C.J x=D.scale*D.J x:= by
      have hJ := hy x hh; rwa [mass, mass, ENNReal.toReal_ofReal (mul_pos h.scale (h.pos x (hp hh))).le, ENNReal.toReal_ofReal (mul_pos ht.scale (ht.pos x (hq hh))).le] at hJ
   have hσ:C.scale=D.scale:= by simpa only [h.anchored,ht.anchored,mul_one] using hx 0 (mem_ball_self hr)
   exact ⟨hσ,fun i hi=> mul_left_cancel₀ (a:=D.scale) ht.scale.ne' ((congr_arg (· * C.J i) hσ.symm).trans (hx i hi))⟩
lemma charge {D:ChartRatio G}(ht:LocalRatio D): C.J=ᶠ[𝓝 0] D.J:= mem_of_superset (ball_mem_nhds _ (lt_min h.patch ht.patch)) fun _ hk=> (shared h ht).2 hk
end Interiors
end YM.MatchingLedger.Compass
