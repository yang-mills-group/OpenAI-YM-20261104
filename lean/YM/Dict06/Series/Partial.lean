import YM.Dict06.Series.Tower

/-! Ordinary iterated derivatives of the homogeneous link packets,
allow distinct held directions. Symmetrize before applying.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Series
open Tensor Function
open scoped BigOperators Topology ContDiff Classical
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- existence sufficient for norms, no Faa di Bruno sum. `gate` carries the
-- common per-direction charge/shape. includes k=0.
lemma all_dirs {k j:ℕ} (T:Tensor.T E F k) (h:Tensor.Sym T) (x:E)(v:Fin j→E)
    (gate:E→Prop)(hx:gate x)(he:∀ i,gate (v i)) :
    ∃ w:Fin k → E, (∀ i, gate (w i)) ∧ iteratedFDeriv ℝ j (Tensor.diagonal T) x v=k.descFactorial j • T w :=by
  induction k generalizing j with
  | zero=>
    refine ⟨Fin.elim0,finZeroElim,?_⟩
    cases j with
    | zero=> rw [Nat.descFactorial_zero,one_smul]
             exact congrArg T (Subsingleton.elim _ _)
    | succ j=>
      rw [show Tensor.diagonal T=fun _=>T Fin.elim0 from funext (fun y=>congrArg T (Subsingleton.elim ..)),iteratedFDeriv_const_of_ne (by omega : j+1≠0), Nat.descFactorial_succ]; simp -- const? fderiv iteratedFDeriv j = const
  | succ k ih =>
    cases j with
    | zero=> refine ⟨fun _=> x,fun _=>hx,?_⟩; simp only [Nat.descFactorial_zero,one_smul]; rfl -- iteratedFDeriv zero
    | succ j=>
      let W:Tensor.T E F k:= ((k+1:ℕ):ℝ) • T.curryLeft (v 0)
      have hW:Tensor.Sym W:=fun i s=>congrArg (((k+1:ℕ):ℝ) • ·) (Tensor.freeze_sym T h (v 0) i s)
      obtain ⟨w,hw,hb⟩:=ih W hW (Fin.tail v) (fun i=>he _)
      have hp : ∀ i:Fin (k+1),gate (Fin.cons (α:=fun _:Fin (k+1)=>E) (v 0) w i):=by
        intro i; refine Fin.cases ?_ ?_ i
        · rw [Fin.cons_zero]; exact he 0
        intro a; rw [Fin.cons_succ]; exact hw a
      refine ⟨Fin.cons (v 0) w,hp,?_⟩
      have hdiag:Analysis.D (v 0) (Tensor.diagonal T)=Tensor.diagonal W:=by
        funext y;rw [Analysis.D,Tensor.differential_diagonal T h]; exact (Nat.cast_smul_eq_nsmul ℝ _ _).symm
      conv_lhs=>rw [← Fin.cons_self_tail v]
      rw [Analysis.cons_inner (Tensor.diag_smooth T _|>.contDiffAt),hdiag,hb,Nat.succ_descFactorial_succ]; unfold W; simp only [smul_apply, ContinuousMultilinearMap.curryLeft_apply,Nat.cast_smul_eq_nsmul, smul_smul, mul_comm]
end YM.Dict06.Series
