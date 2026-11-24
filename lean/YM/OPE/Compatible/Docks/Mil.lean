import YM.OPE.Compatible.Docks.Nurse
/-!
# perturbation
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yolk
open MeasureTheory Function Filter Set
open Lattice RG Wilson Source Labels Source.Drops
open Pill Asymptotics
open Module Finset
open Drift
open scoped Topology BigOperators Classical ContDiff
variable {Lime I E F J X:Type}{k:ℕ} {f:Filter I}{β p:I→ℝ}{s:ℝ}
section
variable [NormedAddCommGroup E][NormedSpace ℝ E]
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
omit [NormedSpace ℝ E] in lemma growUp (h:Tendsto β f atTop) (X:Lime→E) (t:Lime→ℝ) (A:I→Lime) (hp:Wealth X t 1)(ha: Wax β f (t∘A) 0): Wax β f (X∘A) 0:=by
     obtain ⟨c,hc,i,H⟩:=hp; apply RateLE.of_norm_le; swap; · exact Eventually.of_forall fun i=> (H (A i)).trans_eq (mul_one _)
     simpa only [mul_zero,add_zero] using! (RateLE.const c (carth h)).mul (ha.pow i (carth h))
lemma gritC (A B: I → E→L[ℝ] F)(P:I → F→L[ℝ] E)(h:Tendsto β f atTop)(hz:∀ᶠ i in f,A i∘L P i=ContinuousLinearMap.id ℝ F)(hr:s<0)(hh:Wax β f P 0)(hx:Wax β f (B-A) s) : ∃ U: I → F→L[ℝ] E, Wax β f U 0 ∧ ∀ᶠ i in f,B i ∘L U i=ContinuousLinearMap.id ℝ F:=by
      let U(i):= B i ∘L P i; let V:=ContinuousLinearMap.id ℝ F
      have he:Wax β f (fun i=> U i-V) s:=by refine ( (Paintζ (B-A) hh s hx).mono (by linarith)).congr ?_; filter_upwards [hz] with i hi; exact Eq.trans (ContinuousLinearMap.sub_comp ..) (congr_arg (_ - ·) hi)
      have hP:∀ᶠ i in f, ‖U i-V‖≤1/2:=(he.tends hr (carth h)).norm.eventually (ge_mem_nhds (by simp))
      choose! C hc hC using fun (i:I)(hx:‖U i-V‖ ≤1/2)=> WarmInv hx
      let J(i:I):= C i; let u(i:I):= (J i).symm.toContinuousLinearMap; refine ⟨fun i=> P i ∘L u i, (zero_add (0:ℝ) ▸ Paintζ P ?_ 0 hh),?_⟩ -- implicit
      · exact RateLE.absBound 2 (carth h) (hP.mono (fun i hi=>hC i hi))
      filter_upwards [hP] with i hi; ext1 x; exact (DFunLike.congr_fun (hc i hi).symm ((J i).symm x)).trans ((J i).apply_symm_apply _)
end
variable [Fintype J][NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup X][NormedSpace ℝ X]
lemma AlignmentP (p:J→E×E)(q:J→F×F)(A:E→L[ℝ]X)(B:F→L[ℝ]X)(h:∀ i,doublet A (p i)=doublet B (q i)): (doublet A).comp (Arco p)=(doublet B).comp (Arco q):=by
       apply ContinuousLinearMap.ext; intro x; rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,strums,strums]; exact congr_arg (fun f=> Arco f x) (funext h)
end YM.OPE.Yolk
