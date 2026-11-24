import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.Leaves
/-!
# Recovering rapid r derivatives without quotient estimates

Uniform in all non-radius parameters. Useful to strengthen the radial recurrence
 P growth to full Schwartz. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology ContDiff Interval
open ContinuousLinearMap
variable {I E F G A B: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G]
abbrev stack (z:UScale I) (f: I→ Tree E F)(a:I→ℝ)(b:ℕ):= Costs ((path z).slow fun _=>univ) (path z) f (fun i p=> a i / (path z).weight i p.1^b)
abbrev bill (z:UScale I)(a:I→ℝ)(b:ℕ): I→ℝ×E→ℝ:= fun i p=> a i / (path z).weight i p.1^b
abbrev stump (z:UScale I): Cost I (ℝ× E) := (path z).slow fun _=>univ
variable {z: UScale I} {u v: I→ Tree E F}{a:I→ℝ}{b:ℕ}
lemma mulTheory (h:∀ i p,(p.1:ℝ) • u i p=v i p)(hu: stack z u a b)(hv: stack z v a b): stack z (fun i p=> p.1 • fderiv ℝ (u i) p) a b := by
    -- v' = p.1 * u' + u * π
    let X : ℝ× E →L[ℝ] ℝ:= fst ℝ ℝ E; let L : F→L[ℝ](ℝ× E→L[ℝ] F):= smulRightL ℝ (ℝ×E) F X
    have hr : (fun i p=> (p.1:ℝ) • fderiv ℝ (u i) p)=(fun i p=> fderiv ℝ (v i) p - L (u i p)):= by
        funext i p; rw [show v i=(X : ℝ×E→ℝ) • (u i) from funext (fun p=> (h i p).symm), fderiv_smul X.differentiableAt ((hu.smooth _).differentiable (by simp) _),(X.hasFDerivAt).fderiv]; exact (add_sub_cancel_right _ (L (u i p))).symm -- definitional check
    have hV: stack z (fun i=> fderiv ℝ (v i)) a b:= by simpa only [cheap_length,mul_one] using hv.fderiv
    rw [hr]; exact hV.sub (hu.L L)
-- base step
lemma enough0 (h:∀ i p,(p.1:ℝ) • u i p=v i p)(hu: stack z u a b)(hv: stack z v a b): (stump z).Part (path z) u (bill z a (b+1)) 0:= by
    apply Cost.Part.start.mpr; let F (i:I) (p: ℝ×E):= (1+‖p.1‖)⁻¹; let W: I→ ℝ×E→ℝ:=bill z a b; have hN : (stump z).NN F:= fun i p h=> inv_nonneg.mpr (by positivity)
    have T:= (hu.norm_cost.add hv.norm_cost hu.nonneg).cancel hN; refine Cost.Le.left (Cost.Le.right T ?_) (fun i p _=>?_); -- need expose inequality
    · intro i p h; change W i p * F i p ≤ a i / _; simp only [W,F,bill,path,Scale.weight,pow_succ, one_mul,div_mul_eq_mul_div]; exact le_of_eq (by field_simp)
    show ‖u i p‖≤ (‖u i p‖+‖v i p‖)*F i p; rw [← h i p,norm_smul]; apply le_of_eq; unfold F; field_simp
lemma higher (j:ℕ)(h:∀ i p,(p.1:ℝ) • u i p=v i p)(hu: stack z u a b)(hv: stack z v a b): (stump z).Part (path z) u (bill z a (b+1)) j:= by
    induction j generalizing F with -- need generalize instances, u v
    | zero=> exact enough0 h hu hv
    | succ j ih=> apply Cost.Part.next.mpr; convert ih (u:=fun i=> fderiv ℝ (u i)) (v:=fun i p=> p.1 • fderiv ℝ (u i) p) (fun _ _=>rfl) (by simpa only [stack,cheap_length,mul_one] using hu.fderiv) (mulTheory h hu hv) using 1; simp
lemma stack_step (h:∀ i p,(p.1:ℝ) • u i p=v i p)(hu: stack z u a b)(hv: stack z v a b): stack z u a (b+1):= ⟨hu.smooth,fun j=> higher j h hu hv⟩
end YM.MS.Arc
