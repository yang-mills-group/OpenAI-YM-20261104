import YM.FormalOPE.RG10.Boardwalk.Turnstile
/-!
 # Preservation of error rates under norm frame maps & Stock's operations

 At a single horizon! Use localization (strict derivative) so no uniform inverse claims
 on non-small $g$ or actual orbit data. Will need standards on converging chosen geometry.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk
open Function Finset Real Asymptotics Filter Clearing Ledger Rates
open scoped Topology BigOperators Classical
variable {I E F G J R : Type*}{l:Filter I}
variable [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]
variable {P:Path l}{x y:I→E}{x' y':I→ F}{a:E}
namespace Fair
variable (h:Fair P x y)
include h
lemma press {g : E→ F}{D : E→L[ℝ] F}(H: HasStrictFDerivAt g D a)(hz:Tendsto x l (𝓝 a)): Fair P (fun i=>g (x i)) (fun i=>g (y i)):= by
 obtain ⟨K,U,hU,hK⟩:= H.exists_lipschitzOnWith; refine ⟨Sized.income _ (H.continuousAt.tendsto.comp hz), h.shift.done (K:ℝ) K.property ((Filter.Eventually.and (hz.eventually hU) ((h.both _ hz).eventually hU)).mono fun i hh=> ?_)⟩; exact lipschitzOnWith_iff_norm_sub_le.mp hK hh.1 hh.2
lemma pairing (h' : Fair P x' y') : Fair P (fun i=> (x i,x' i)) (fun i=>(y i,y' i)):= by
 let a:= ContinuousLinearMap.inl ℝ E F; let b:=ContinuousLinearMap.inr ℝ E F
 exact ((h.map a).join (h'.map b)).fit (Eventually.of_forall fun i=>by simp [a,b]) (Eventually.of_forall fun i=>by simp [a,b])
lemma inspect {u v:I→ E→L[ℝ] F} (he:Fair P u v) : Fair P (fun i=> u i (x i)) (fun i=> v i (y i)):= h.bilinear he (ContinuousLinearMap.apply ℝ F)
omit h
lemma questionnaire [Fintype J]{x y:I→ J→ E} (hz:∀ j, Fair P (fun i=>x i j) (fun i=>y i j)): Fair P x y:= by
 classical
 have hm u: (∑ i:J, ContinuousLinearMap.single ℝ (fun _:J=>E) i (u i))=u:= by simp [LinearMap.sum_single_apply] -- inspect
 exact (Fair.sum Finset.univ (fun (i:J) _=> (hz i).map (ContinuousLinearMap.single ℝ (fun _:J=>E) i))).fit (Eventually.of_forall fun i=> hm (x i)) (Eventually.of_forall fun i=> hm (y i))

variable [NormedRing R][NormedAlgebra ℝ R] -- CLM inverse may require NormOneClass
variable {p q u v:I→ R} (H: Fair P p q)
include H
lemma invert [CompleteSpace R] {K:R}(hx:IsUnit K)(hz:Tendsto p l (𝓝 K)) : Fair P (fun i=>Ring.inverse (p i)) (fun i=>Ring.inverse (q i)):= by
 obtain ⟨u,rfl⟩:=hx; exact H.press (hasStrictFDerivAt_ringInverse u) hz -- infer
lemma mul (h : Fair P u v) : Fair P (fun i=>p i * u i) (fun i=>q i*v i):= H.bilinear h (ContinuousLinearMap.mul ℝ R)
lemma pow (n:ℕ) : Fair P (fun i=> (p i)^n) (fun i=> (q i)^n):= by induction n with
 | zero=>simpa only [pow_zero] using! Fair.fixed (1:R)
 | succ n ih=> simpa only [pow_succ] using! ih.mul H
-- fix include H in lean section
end Fair
end YM.FormalOPE.RG10.Boardwalk
