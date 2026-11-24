import YM.MS.Drops.Pulse
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-! Radian to MS chart.
Dimension fixed=4. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Drops
open Set Function Filter Finset Metric MeasureTheory Real
open Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Analysis Labels Maxwell Theater Next Next.Rank Next.Rank.Beamer Tone High Rake Osc Snap
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
abbrev τ:ℝ:= 2*π
def ν : E4≃L[ℝ] FourP:= (Theater.out.trans (LinearEquiv.smulOfNeZero ℝ FourP τ (by unfold τ; positivity))).toContinuousLinearEquiv -- name
lemma fp (x:E4): ν x=τ • out x:= rfl
lemma fourFπ : Module.finrank ℝ FourP=4:= Eq.trans ( out.finrank_eq|>.symm ) Radian.spaceD
lemma phaseFπ (x:E4)(t:Axis): ν x t=τ*x t:= rfl
lemma ampFπ : MeasurePreserving ν volume planeF:= by
    let L : E4→ FourP:= WithLp.ofLp; let Q: Measure FourP:= volume; refine ⟨ ν.continuous.measurable,?_⟩; rw [show ⇑ν = (fun p:FourP=>τ • p) ∘ L from funext fp, ← Measure.map_map (measurable_const_smul _) ((PiLp.volume_preserving_ofLp Axis).measurable), (show Measure.map L volume= Q from ( PiLp.volume_preserving_ofLp Axis ).map_eq), Measure.map_addHaar_smul Q (by unfold τ; positivity), fourFπ,abs_of_nonneg (inv_nonneg.mpr ( by unfold τ; positivity )) ]; unfold planeF covMeasure; rw [ show Fintype.card Axis=4 from Fintype.card_fin _ ]
lemma ν_bill (x y:E4): Tone.bill (out x) (ν y)=Radian.wave x y:= by
    have he : inner ℝ y x=Momentum.pairing (out x) ( out y ):= by rw [ EuclideanSpace.inner_eq_star_dotProduct, star_trivial ]; rfl
    rw [ bill,Radian.wave, inner_neg_right,neg_neg, he,Real.fourierChar_apply ]; change Complex.exp _= Complex.exp _; rw [show Momentum.pairing ( out x ) (ν y)= τ * Momentum.pairing ( out x ) ( out y ) from ?_]; congr 1; unfold τ; push_cast; ring
    unfold Momentum.pairing; rw [ Finset.mul_sum ]; exact Finset.sum_congr rfl fun _ _=> mul_left_comm ..
lemma ν_sq (x:E4): Momentum.sq (ν x)= τ^2*‖x‖^2:= by rw [fp, scaling ]; congr; rw [EuclideanSpace.norm_sq_eq]; unfold Momentum.sq; exact Finset.sum_congr rfl fun i _=> by simp -- name
end YM.MS.Drops
