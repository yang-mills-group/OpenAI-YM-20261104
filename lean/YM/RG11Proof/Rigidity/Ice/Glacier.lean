import YM.RG11Proof.Rigidity.Ice.Inert

/-!
# No change on the measured correlations along the analytic b flow
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Labels Pert.Position Pert Maxwell Function Extra.FD NormedSpace Filter
open scoped Classical BigOperators Topology ContDiff Real

variable {G : Gauge} {F : Frames G} {d r:ℕ}
abbrev P (F : Frames G)(d r:ℕ):= Fin r→E F d
private lemma holds (v : MultilinearMap ℂ (fun _:Fin r=> E F d) ℂ) : Continuous v := by
  let U := tower F d
  have he (p:P F d r) : v p=∑ i:Fin r→U.toBasis.J, (∏ j, U.b.equivFun (p j) (i j))*v (fun j=> U.b (i j)) := by
    conv_lhs=>rw [←funext (fun i=> U.b.sum_equivFun (p i))]
    rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ]
    simp_rw [MultilinearMap.map_smul_univ,smul_eq_mul]
  rw [funext he]
  exact continuous_finsetSum _ fun i _=> (continuous_finsetProd _ fun j _=> ((continuous_apply (i j)).comp (U.b.equivFun.toLinearMap.continuous_of_finiteDimensional)).comp (continuous_apply j)).mul continuous_const

variable {b : Buffer F d}
lemma Frigid.stay (h : Frigid b)(p:P F d r)(x: Points r)(hx : x∈conf r)(t : ℝ):
    visible F d x (fun i=> drive b.val (p i) t)= visible F d x p := by
  let v : ContinuousMultilinearMap ℂ (fun _:Fin r=>E F d) ℂ:=⟨visible F d x, holds _⟩
  let w := v.restrictScalars ℝ
  let u (t:ℝ)(i:Fin r):= drive b.val (p i) t
  let f : ℝ → ℂ := w ∘ u
  have ht i (t:ℝ):HasDerivAt (fun s=>u s i) (b.val (u t i)) t:=march b.val _ _
  have he (t : ℝ) : HasDerivAt f 0 t:=by
    have he:HasDerivAt u (fun i=> b.val (u t i)) t:= hasDerivAt_pi.mpr (fun i=> ht i _)
    have hg := (w.hasFDerivAt (u t)).comp_hasDerivAt _ he
    refine hg.congr_deriv ?_
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    exact h _ _ _ hx
  calc _ = f 0:= is_const_of_deriv_eq_zero (fun t=> (he t).differentiableAt) (fun t=> (he t).deriv) t 0
       _ = _ := by change visible F d x (fun i=> drive b.val (p i) 0)=_; simp_rw [starts]

end YM.RG11.Rigidity.Ice
