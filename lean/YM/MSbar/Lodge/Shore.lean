import YM.MSbar.Lodge.Road
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lodge
open Function Filter Whisk Lis Measuring Cacao Aqua RawP Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι M:Type}[Fintype σ]
variable {σ ι M:Type}[Fintype σ][Fintype ι][MeasurableSpace M]{μ:MeasureTheory.Measure M}[MeasureTheory.IsProbabilityMeasure μ]
open MeasureTheory Set Metric
local notation "Π"=>Positions σ
local notation "Λ"=>Positions ι
variable {k p:ℕ}{C D θ:ℝ}{F:Positions σ→ℝ}(h:ContDiff ℝ k F)
noncomputable def shore (μ: Measure M)(P:Positions ι→L[ℝ] Positions σ)(W:M→ Positions σ)(F:Positions σ→ℝ)(y:Positions ι) := ∫ i,F (W i+P y)∂μ
variable (P:Positions ι→L[ℝ]Positions σ) (W:M→ Positions σ) (hW:Measurable W)
variable (x:Positions ι)
local notation "Y"=> shore μ P W F
-- bounds pointwise native coords implies ∥D all∥ up to fixed tor. prove using List roc only. continuous_meas_fderiv from smooth
structure Curb (k:ℕ)(F:Positions σ→ℝ):Prop where
   paid : ∀ l:List σ,l.length≤ k → ∃ B:ℝ,∀ x, |buoy F x l| ≤ B
variable (hp:Curb k F)
include h hp
lemma meter (l:List Π)(he:l.length≤k):∃ B:ℝ, 0 ≤B∧∀ x, |roc F l x| ≤ B:=by
    have hu (l:List Π) (t:List σ) (he:t.length+l.length ≤ k): ∃ B:ℝ,0 ≤ B ∧∀ x, |roc F ((t.map (@bolt σ))++l) x|≤ B:=by
        induction l generalizing t with
        | nil=> obtain ⟨B,hB⟩:= hp.paid t (by simpa only [List.length_nil,add_zero] using he); exact ⟨B,(abs_nonneg _).trans (hB 0), fun x=> by simpa only [List.append_nil,buoy] using hB x⟩
        | cons a l ih=>
           choose v hv hh using fun i:σ=> ih (t++[i]) (by simp only [List.length_append,List.length_cons,List.length_nil] at *;omega)
           refine ⟨∑ i:σ,|a i| *v i, Finset.sum_nonneg (fun i _=> mul_nonneg (abs_nonneg _) (hv i)),fun x=>?_⟩; nth_rw 1 [spiral a,mash _ _ _ _ _ _ _ h.contDiffAt]; refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _=>?_); rw [abs_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.nil_append,List.cons_append] using hh i x; rw [List.length_map]; rw [List.length_cons] at he; omega; exact a -- args
    exact hu l [] (by simpa)
include hW
lemma issue (i:List Π)(x: Positions ι)(he:i.length≤k): Integrable (fun z=> roc F i (W z+ P x)) μ:=by
    have ht:Continuous (roc F i):= continuous_iff_continuousAt.mpr fun v=> (Lis.smooth k 0 i h.contDiffAt (by omega)).continuousAt; obtain ⟨B,_,hh⟩:= meter h hp i he; exact Integrable.of_bound (ht.measurable.comp (hW.add measurable_const)|>.aestronglyMeasurable) B (ae_of_all _ fun i=> hh _)
lemma capsule (l:List (Positions ι))(he:l.length≤k) : roc (shore μ P W F) l x=∫ z,roc F (l.map P) (W z+P x)∂μ:=by
    induction l generalizing x with
    | nil=>rfl
    | cons a l ih=>
       let t:=List.map P l; let V(y:Λ)(z:M):= W z+ P y; let f:= roc F t; let E(y):= f ∘ V y; let L(y): M→ Λ →L[ℝ]ℝ:=fun i=> (fderiv ℝ f (V y i)).comp P
       have hE(x): roc (shore μ P W F) l x=∫ z,E x z∂μ:= ih x (by simp only [List.length_cons] at he; omega)
       have hz:t.length<k:=by unfold t; rw [List.length_cons] at he; rw [List.length_map]; omega
       have ht(z):ContDiffAt ℝ 1 f z:= (show ContDiffAt ℝ (↑(1:ℕ)) f z from Lis.smooth k 1 t h.contDiffAt (by omega)); have hf:ContDiff ℝ 1 f:= contDiff_iff_contDiffAt.mpr ht
       have hv(y:Λ): Integrable (E y) μ:= issue h P W hW hp t _ hz.le -- order
       have hx: Measurable (L x):=by let Z:Π→L[ℝ]ℝ:= 0; have he:Continuous (fun i:Π→L[ℝ]ℝ=> i.comp P):= continuous_id.clm_comp continuous_const; exact he.measurable.comp ((hf.continuous_fderiv (by norm_num)|>.measurable).comp (hW.add measurable_const))
       choose B hB hg using fun i:ι=> meter h hp (P (bolt i)::t) (by rw [List.length_cons]; omega)
       let B':=∑ i:ι,B i; have hh(y:Λ)(z:M) : ‖L y z‖ ≤ B':=by
            refine (L y z).opNorm_le_bound (show 0≤B' from Finset.sum_nonneg (fun i _=> hB i)) ?_; intro v; nth_rw 1 [spiral v]; rw [map_sum]; unfold B'; rw [sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>?_)); rw [map_smul,norm_smul,mul_comm ‖v i‖]; exact mul_le_mul (hg i _) (norm_le_pi_norm v i) (norm_nonneg _) (hB i)
       have hl: HasFDerivAt (fun x=> ∫ i,E x i ∂μ) (∫ i,L x i∂μ) x:=hasFDerivAt_integral_of_dominated_of_fderiv_le (F:=E) (F':=L) (s:=Set.univ) Filter.univ_mem (Eventually.of_forall fun y=> (hv y).aestronglyMeasurable) (hv x) hx.aestronglyMeasurable (ae_of_all μ fun i y _=> hh y i) (integrable_const _) (ae_of_all μ fun i y _=>?_)
       swap
       · exact ((ht (V y i)|>.differentiableAt (by simp)).hasFDerivAt.comp y (P.hasFDerivAt.const_add (W i)))
       have hh': Integrable (L x) μ:= Integrable.of_bound hx.aestronglyMeasurable B' (ae_of_all μ (hh _)); rw [roc,show roc (shore μ P W F) l= _ from funext hE,hl.fderiv,ContinuousLinearMap.integral_apply hh']; rfl
end YM.MSbar.Lodge
