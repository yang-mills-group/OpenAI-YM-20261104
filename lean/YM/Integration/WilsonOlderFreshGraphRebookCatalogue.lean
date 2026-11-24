import YM.Integration.WilsonOlderFreshGraphPostedLaunch

/-! An authenticated normalized unary roll can use the receiving school's
order and census cap, at the very same already paid radius and expense.
The grades and the unique active mark are read from the true roll. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphRebookCatalogue
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open QuadraticLocal.Sunrise WilsonOlderFreshGraphSlate WilsonOlderFreshGraphArmada
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{d Q:ℕ}{σ:ℝ}(T:Copy G d Q σ)
variable {P:Passport n Unit}{R:Census Unit}(S:Binder P R)(A:Unit → Set ℂ)
variable {w b:ℝ}{oldOrder oldPieces oldShelf:ℕ}

theorem original (earned:Armada (T.rows S A) (fun _:Unit=>w) (fun _:Unit=>d) σ b
    oldOrder oldPieces oldShelf) {p seats h:ℕ}(issued:Q ≤ p)(room:1 ≤ seats)(tall:d ≤ h):
    Armada (T.rows S A) (fun _:Unit=>w) (fun _:Unit=>d) σ b p seats h:=by
  refine ⟨⟨?_,?_⟩,earned.positive,earned.suggests,⟨earned.purchases.spend,?_⟩,earned.honor⟩
  · intro s
    exact (Finset.card_le_univ _).trans (by simpa using room)
  · intro s
    have bound:(∑ _i∈s.val,d)≤ ∑ _i:Unit,d:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _)
    exact bound.trans (by simpa using tall)
  · intro z
    change z.1.val ≤ p ∧ d=∑ _v∈S.mode.val,d
    exact ⟨(Nat.le_of_lt_succ z.1.isLt).trans issued,by simp [full_mode S]⟩

end YM.Integration.WilsonOlderFreshGraphRebookCatalogue
end
