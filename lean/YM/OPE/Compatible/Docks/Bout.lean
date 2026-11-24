import YM.OPE.Compatible.Ingle.Hock
/-!
# coordinate costs CL marks of BOTH real components before ray projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yolk
open MeasureTheory Function Filter Set
open Lattice RG Wilson Source Labels Source.Drops
open Pill Asymptotics
open scoped Topology BigOperators Classical ContDiff
variable {I E F J X:Type}{k:ℕ} {f:Filter I}{β p:I→ℝ}{s:ℝ}
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup X][NormedSpace ℝ X]{ρ η: I→ℝ} {w w': I→ E→L[ℝ] F}{v:I→ X→L[ℝ] E}
local notation "hR"=> Wax β f
lemma Paintζ [NormedAddCommGroup J][NormedSpace ℝ J](p: I→ F→L[ℝ] J)(h:hR w s) (t:ℝ)(hx:hR p t) : hR (fun i=>p i ∘L w i) (t+s):= hx.bil h (Eventually.of_forall fun _=>ContinuousLinearMap.opNorm_comp_le ..)
def doublet (p:E→L[ℝ] F):(E×E)→L[ℝ] F×F:= (p.comp (.fst ..)).prod (p.comp (.snd ..))
lemma doublePrice (p: E→L[ℝ] F) : ‖doublet p‖≤ ‖p‖:=by
       refine (doublet p).opNorm_le_bound (norm_nonneg _) (fun a=>?_); rw [Prod.norm_def]; refine max_le ?_ ?_;
       · exact (p.le_opNorm a.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le ..) (norm_nonneg _))
       exact (p.le_opNorm a.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le ..) (norm_nonneg _))
lemma twins (h:hR w s): hR (fun i=>doublet (w i)) s := h.transfer (Eventually.of_forall fun i=>doublePrice (w i))
-- complex assembly paying Vak.
variable [Fintype J]
noncomputable def Az (v:E × E):ℂ→L[ℝ] E×E := Complex.reCLM.smulRight v + Complex.imCLM.smulRight (-v.2,v.1)
lemma Aroma (v: E×E): ‖Az v‖≤ (‖Complex.reCLM‖+‖Complex.imCLM‖)*‖v‖:= by
       let U:E×E:= (-v.2,v.1); have hp : ‖U‖=‖v‖:=by simp [U,Prod.norm_def,max_comm]
       unfold Az; rw [add_mul]; refine (norm_add_le ..).trans (add_le_add ?_ ?_); exact le_of_eq (ContinuousLinearMap.norm_smulRight_apply ..); rw [ContinuousLinearMap.norm_smulRight_apply, ← hp]
noncomputable def Arco (v:J→E×E):(J→ℂ)→L[ℝ] E×E:= ∑ i:J, (Az (v i)).comp (ContinuousLinearMap.proj i)
lemma bWire (v:J→E×E)(x:J→ℂ): Arco v x=∑ i:J, Az (v i) (x i):= by unfold Arco; rw [_root_.sum_apply];rfl
lemma portF (z:I→ J→ E × E)(h:∀ j: J,hR (fun i=> z i j) s)(hp:Tendsto β f atTop): hR (fun i=> Arco (z i)) s:=by
       have hv:= carth hp; apply RateLE.sum (S:=Finset.univ) (f:=fun i j=>(Az (z j i)).comp (ContinuousLinearMap.proj i)) hv; intro i _; let c:= ‖Complex.reCLM‖+‖Complex.imCLM‖; have hQ:hR (fun j=> Az (z j i)) s:= RateLE.of_norm_le (zero_add s ▸ ((RateLE.const c hv).mul (h i|>.norm))) (Eventually.of_forall fun j=>Aroma _); exact add_zero s ▸ Paintζ _ (RateLE.const _ hv) s hQ
lemma blend (p:E→L[ℝ] F)(t:ℂ)(v:E×E): doublet p (Az v t)= Az (doublet p v) t:=by ext <;> simp [doublet,Az] -- names
lemma strums (p:E→L[ℝ] F)(w:J→ E×E)(x:J→ℂ): doublet p (Arco w x)= Arco (fun i=>doublet p (w i)) x:=by rw[bWire,bWire,map_sum]; exact Finset.sum_congr rfl fun _ _=> blend ..
lemma Vortex (v:E×E)(r:ℂ) : Az v (Complex.I*r)=(-(Az v r).2,(Az v r).1):=by ext<;>simp [Az]; abel
lemma phaseI (v:J→E×E)(x:J→ℂ) : Arco v (Complex.I • x)= (-(Arco v x).2,(Arco v x).1):=by
        simp_rw [bWire,Pi.smul_apply,smul_eq_mul,Vortex]; apply Prod.ext <;> simp [Prod.fst_sum,Prod.snd_sum,Finset.sum_neg_distrib]
lemma chordMem (v:J→E×E)(j:J): Arco v (Pi.single j 1)= v j:=by rw [bWire, Finset.sum_eq_single j,Pi.single_eq_same]; unfold Az; simp; intro i hi h; rw [Pi.single_eq_of_ne h,map_zero]; simp -- tactic grouping
end
end YM.OPE.Yolk
