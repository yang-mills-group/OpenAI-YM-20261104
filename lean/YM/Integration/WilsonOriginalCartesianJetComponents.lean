import YM.Integration.WilsonOriginalSpatialProductRule

/-! Actual Cartesian components of the Fréchet jet, with the order of
evaluated directions kept throughout the open chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCartesianJetComponents
open Set Filter
open WilsonOriginalSupportedBoxChart (Space)
open WilsonOriginalSpatialProductRule (word step Regular)
open scoped Topology ContDiff

theorem original {d : ℕ} (j : ℕ) (axis : Fin j → Fin d) (f : Space d → ℂ)
    {O : Set (Space d)} (room : IsOpen O) (sf : Regular O f) :
    EqOn (fun x => iteratedFDeriv ℝ j f x (fun k => Pi.single (axis k) (1:ℝ)))
      (word (List.ofFn axis).reverse f) O := by
  induction j with
  | zero =>
    intro x _
    simp [word]
  | succ j ih =>
    intro x hx
    let tail : Fin j → Fin d := fun k => axis k.succ
    have entered : (fun y => iteratedFDeriv ℝ j f y (fun k => Pi.single (tail k) (1:ℝ)))
        =ᶠ[𝓝 x] word (List.ofFn tail).reverse f := by
      filter_upwards [room.mem_nhds hx] with y hy using ih tail hy
    have smooth : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
      (sf x hx).differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top j)
    dsimp only
    rw [smooth.iteratedFDeriv_succ_apply_left']
    change (fderiv ℝ (fun y => iteratedFDeriv ℝ j f y (fun k => Pi.single (tail k) (1:ℝ))) x)
      (Pi.single (axis 0) (1:ℝ)) = _
    rw [entered.fderiv_eq,List.ofFn_succ,List.reverse_cons,WilsonOriginalSpatialProductRule.append]
    rfl

end YM.Integration.WilsonOriginalCartesianJetComponents
