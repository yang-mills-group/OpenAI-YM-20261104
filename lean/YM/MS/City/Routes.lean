import YM.MS.City.Perk
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
/-!
# Cov-torus loop measure invariance

No cut ambiguity. For load-lines in both line directions q and shifted by other
 (continuous, not momentum-lattice-period) offsets, preserve the integral of the
 actual periodic function as in the contour comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.City
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame
open Complex (I)
open scoped Topology ContDiff Interval
variable {G:Gauge}{F:QP→ℂ} (μ:Measure QP)
def vol : Measure QP:= Measure.pi (fun _:Axis=> cap)
lemma partInt (F:QP→ℂ)(h:Continuous F): Integrable F vol:= by
   let m:=μzone; have hv :=Tone.integr F h; rw [μview] at hv; exact (integrable_smul_measure (by positivity) (by finiteness)).mp hv
lemma restrictN [μ.IsNegInvariant] (r:ℝ) : Measure.IsNegInvariant (μ.restrict (Metric.closedBall 0 r)):= by
   let X:= Metric.closedBall (0:QP) r; let N:= ((Homeomorph.neg QP).toMeasurableEquiv);
   constructor; -- ∀ (s?)
   show Measure.map N _ = _; change Measure.map N (μ.restrict X)= _
   nth_rw 1 [show X= N ⁻¹' X from by ext; simp [N,X, Metric.mem_closedBall] ]; rw [← N.measurableEmbedding.restrict_map]; exact congr_arg (fun μ:Measure QP=>μ.restrict X) (Measure.measurePreserving_neg μ).map_eq
lemma capN : Measure.IsNegInvariant μzone:= restrictN _ _ -- covMeasure neg?
-- decompose single shift via univ type
abbrev A (i:Axis): QP ≃ᵐ ℝ × (Fin 3→ℝ) := MeasurableEquiv.piFinSuccAbove _ i
lemma deck (F:QP→ℂ)(h:Continuous F)(i:Axis): (∫ x,F x ∂vol)=∫ x:Fin 3→ℝ, (∫ y:ℝ,F ((A i).symm (y,x)) ∂cap) ∂Measure.pi (fun _=>cap) := by
   let μ:Measure (Fin 3→ℝ) := Measure.pi fun _=>cap; have he : MeasurePreserving (A i) vol (cap.prod μ):= measurePreserving_piFinSuccAbove _ i
   let f (x:ℝ × (Fin 3→ℝ)) := F ((A i).symm x); have hk : Integrable f (cap.prod μ):= he.symm.integrable_comp_of_integrable (partInt F h)
   rw [← he.symm.integral_comp']; exact integral_prod_symm _ hk
lemma capIntegral (f:ℝ→ℂ)(hh: Periodic f (2*π))(b:ℝ): (∫ x,f (b+x) ∂cap)=∫ x,f x ∂cap:=by
   let h : -π≤π:= by linarith [pi_pos]
   unfold cap; rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h, intervalIntegral.integral_comp_add_left f b,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le h]; simpa only [show b+ -π + 2*π=b+π by ring,show -π+2*π=π by ring] using hh.intervalIntegral_add_eq (b+ -π) (-π)
def addone (i:Axis)(b:ℝ): QP:= Pi.single i b
lemma layerOne (x:Fin 3→ℝ)(i:Axis)(a b:ℝ): (A i).symm (b+a,x)= addone i b + (A i).symm (a,x):= by
   apply funext; refine i.forall_iff_succAbove.mpr ?_ -- equality at j consumed variable?
   exact ⟨by simp [A,addone],fun k=>by simp [A,addone,Fin.succAbove_ne]⟩
lemma imageOne (i:Axis): addone i (2*π)= rep (step i):= by ext j; simp [rep,addone,Pi.single_apply,emb_step]

abbrev Gate (F:QP→ℂ): Prop:= ∀ i:Cover, Periodic F (rep i)
lemma byone (H:Gate F)(h:Continuous F)(i:Axis)(b:ℝ) : (∫ x,F (addone i b+x) ∂vol)=∫ x,F x ∂vol:= by
   rw [deck (fun x=>F (addone i b+x)) (by fun_prop) i,deck F h i]; apply integral_congr_ae; filter_upwards with x; simp_rw [← layerOne]; refine capIntegral (fun y=> F ((A i).symm (y,x))) ?_ b; intro y; dsimp only; rw [add_comm y,layerOne,imageOne,add_comm]; exact H ..
lemma moves (x:QP)(h:Continuous F)(H:Gate F): (∫ t,F (x+t) ∂μzone)=∫ t,F t ∂μzone:= by
   rw [μview,integral_smul_measure,integral_smul_measure]; congr 1
   have he (s:Finset Axis): (∫ t,F ((∑ i ∈ s, addone i (x i))+t) ∂vol) = ∫ t,F t ∂vol:= by
      induction s using Finset.induction_on with
      | empty=> simp
      | insert a s ha ih=>
        let X:=∑ i∈s,addone i (x i); let T:= fun t=> F (X+t); have hT : Gate T := fun i u=> by unfold T; rw [← add_assoc,H i]
        simp_rw [Finset.sum_insert ha, add_comm (addone a _),add_assoc]; rw [← ih]; exact byone hT (h.comp (continuous_const.add continuous_id)) a (x a)
   have hx : ∑ i:Axis,addone i (x i)=x:=by ext t; simp [Finset.sum_apply,addone,Pi.single_apply]
   have hv:= he Finset.univ; rw [hx] at hv; exact hv
end YM.MS.City
