import YM.Integration.WilsonOlderFreshGraphRebookCatalogue

/-! Every row in the very same one-name gallery keeps its actual receipts at
the physical pole depth. This applies both to the independent issued row and
to the original student's complete emitted roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphSingleShelf
open Lattice Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open scoped Classical BigOperators

theorem original {G:Gauge}{n:Side}{P:Passport n Unit}{R:Census Unit}{ι α:Type}
    (X:ι→Row P R G α)(w:Unit→ℝ)(d p seats h:ℕ)(σ b:ℝ)
    (earned:Armada X w (fun _=>d) σ b p seats h):
    Armada X w (fun _=>d) σ b p seats d:=by
  refine ⟨⟨earned.quota,?_⟩,earned.positive,earned.suggests,earned.purchases,earned.honor⟩
  intro s
  have allot:(∑ _v∈s.val,d)≤ ∑ _v:Unit,d:=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _)
  simpa using allot

end YM.Integration.WilsonOlderFreshGraphSingleShelf
end
