import YM.Integration.WilsonOriginalMixedBlockIncome

/-! Normalize the true rooted binder income by the prescribed individual physical salaries.
Disjoint names are charged only on their own occupied block. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedBlockBudget
open Function Finset Lattice Laurent RG Wilson Marker Multi Gauge
open Push Push.AbsoluteSums Push.Local Paths Animals ConnectedActivityE6 QuadraticLocal
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonOriginalMixedBlockIncome
open scoped Classical BigOperators

variable {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
    {n:Side} {P:Passport n V} (B:I→Earn.Binder P (Stock.census V))
def roots (a:I→ℝ):ℝ:=Finset.univ.sup' Finset.univ_nonempty fun x:Site n=>
  ∑j, if (B j).center=x then a j else 0

theorem original (σ:ℝ)(cash a:I→ℝ)(H:V→ℝ)(positive:∀v,0 < H v)
    (source:∀j,Real.exp (σ*(B j).length)*cash j ≤ Poly.toll H (B j).mode*a j):
    bill B σ cash (fun v=>(H v)⁻¹) ≤ roots B a:=by
  apply Finset.sup'_le
  intro x _
  apply le_trans _ (Finset.le_sup' (fun y:Site n=>∑j,if (B j).center=y then a j else 0) (mem_univ x))
  apply Finset.sum_le_sum
  intro j _
  by_cases here:(B j).center=x
  · simp only [WilsonOriginalMixedBlockIncome.weight,if_pos here,mul_assoc]
    have tsh:Poly.toll (fun v=>(H v)⁻¹) (B j).mode=(Poly.toll H (B j).mode)⁻¹:=by simp [Poly.toll]
    rw [tsh]
    calc (Poly.toll H (B j).mode)⁻¹*(Real.exp (σ*(B j).length)*cash j) ≤
        (Poly.toll H (B j).mode)⁻¹*(Poly.toll H (B j).mode*a j):=
          mul_le_mul_of_nonneg_left (source j) (inv_nonneg.mpr (Poly.worth positive _).le)
      _=a j:=by rw [←mul_assoc,inv_mul_cancel₀ (Poly.worth positive _).ne',one_mul]
  · simp [WilsonOriginalMixedBlockIncome.weight,here]

end YM.Integration.WilsonOriginalMixedBlockBudget
end
