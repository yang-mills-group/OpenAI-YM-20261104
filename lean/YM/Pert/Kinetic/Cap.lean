import YM.Pert.Kinetic.Panel
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson RG MeasureTheory Asymptotics Bid Source
open Work.F03
open scoped Topology BigOperators Classical ContDiff
variable {n:Side}{G:Gauge}
lemma small_beta {R W : Rep G n} {σ' C' Λ' δ' w' σ C Λ δ w s:ℝ} (hG:G.Simple) (h : R.eval=W.eval) (hW : W.Lawful σ' C' Λ' δ' w') (hR : R.Lawful σ C Λ δ w)
  (h₁ : Quotes R.p σ C Λ δ s) (h₂ : Quotes W.p σ' C' Λ' δ' s) (hn : 4≤n.val) (hS : |R.beta| ≤ s) (ht : Real.pi^2 * (Full.mesh n) * (2 * (Fintype.card PlaqAxes:ℝ) * s^9) ≤ 1/2) : |R.beta-W.beta| ≤ (4*Real.pi^2*coefK*s^9) * (Full.mesh n) := by
     let u:=|R.beta-W.beta|
     have hh : |W.beta| ≤ s+u := by unfold u;rw [abs_sub_comm]; linarith only [abs_sub_abs_le_abs_sub W.beta R.beta,hS] -- broken
     have h₀:=error_of_cost R W hG hR hW hn h
     have h₃:= add_le_add (paid_quote h₁ (show (0:ℝ)≤0 from le_rfl) (le_of_le_of_eq hS (add_zero s |>.symm))) (paid_quote h₂ (abs_nonneg _) hh)
     let v:=Real.pi^2*(Full.mesh n)*coefK*s^9
     suffices H:u ≤ 2*v+u/2 by nlinarith only [H]
     have hs:=h₁.pos
     calc u ≤ (Real.pi^2*(Full.mesh n))*(billTotal R.p σ C Λ R.beta δ + billTotal W.p σ' C' Λ' W.beta δ') := h₀.trans (le_of_eq (by ring))
          _ ≤ _ * ((coefK*s^9+coefK*s^9)+(2*(Fintype.card PlaqAxes:ℝ)*s^9*u)) := mul_le_mul_of_nonneg_left (h₃.trans_eq (by ring)) (mul_nonneg (sq_nonneg _) Full.mesh_pos.le)
          _ ≤ _ := by have hp:=mul_le_mul_of_nonneg_right ht (abs_nonneg (R.beta-W.beta));dsimp only [v,u];linarith only [hp]
end YM.Pert.Kinetic
