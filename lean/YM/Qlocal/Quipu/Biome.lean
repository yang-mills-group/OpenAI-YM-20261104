import YM.Qlocal.Quipu.Vector
/-! Diagonal occupation of actual Hector.V Legendre predictor shapeshift. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Two
open AllOrder AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method GaussianScore Module Kinetic
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β σ: Type} [Fintype α] [Fintype β] [Fintype σ] {k N M:ℕ} {a C D b:ℝ}
section rig
variable [DecidableEq α][DecidableEq β][DecidableEq σ]
variable (K : Stalk β β) (x:rule (α⊕β) n)
-- project arbitrary stalk β across α, keep α spec.
def plant (α:Type) [DecidableEq α] (K: Stalk β β) : Stalk (α⊕β) (α⊕β)
 | Sum.inr i, Sum.inr j=> K i j
 | Sum.inl i, Sum.inl j=> Work.F08.unitRow α i j
 | _, _=> 0
lemma cents (h:Belt K a C): Belt (plant α K) a (max C 1):= by
   intro i j; rcases i with (i|i) <;> rcases j with (j|j);
   · exact (Work.F08.strip_unit i j).mono le_rfl (le_max_right ..) -- args inspect
   · simp only [plant,Width,SumBudget]; simp [zero_le_one.trans (le_max_right C 1)] -- repeat
   · simp only [plant,Width,SumBudget]; simp [zero_le_one.trans (le_max_right C 1)]
   exact (h i j).mono le_rfl (le_max_left ..)
local notation "P"=> plant α K
lemma site_right : here Sum.inr (know (P) n x) = know K n (here Sum.inr x):= by
 funext i; change ∑ j:Leaf n (α⊕β), direct (P) n _ j*x j=_; rw [cut_sum, Finset.sum_eq_zero ?_,zero_add]; · rfl
 intro j _; rw [show direct (P) n (up Sum.inr i) (lead β j)=0 from ?_,zero_mul]; unfold direct; simp [plant, here, up, lead]
lemma site_left : here Sum.inl (know (P) n x)=here Sum.inl x:=by
 funext i; change ∑ j:Leaf n (α⊕β), direct (P) n _ j*x j=_; rw [cut_sum]; nth_rw 2 [Finset.sum_eq_zero ?_];
 · rw [add_zero]; change (direct (Work.F08.unitRow α) n *ᵥ (here Sum.inl x)) i= _; rw [(paid_identity (a:=0) n).2, Matrix.one_mulVec]
 intro j _; simp [direct,plant,peg,up,here] -- fill
-- equivalence F₊, rather than sum lemmas in post
variable (E:σ ≃ α⊕β) (y:rule σ n)
def parallel (E:σ ≃ α⊕β)(K:Stalk β β): Stalk σ σ:= fun i j=> plant α K (E i) (E j)
local notation "Q"=> parallel E K
lemma income (h:Belt K a C) : Belt Q a (max C 1):= fun i j=> cents K h (E i) (E j)
lemma based : here E.symm (know Q n y) = know (P) n (here E.symm y):=by
 let F:= Equiv.prodCongr (Equiv.refl (Site n)) E.symm; ext1 i; change (∑ j:Leaf n σ,direct Q n (F i) j*y j) = (∑ j:Leaf n (α⊕β),direct _ n i j * y (F j)); rw [← Equiv.sum_comp F]; exact Finset.sum_congr rfl (fun j _=> by unfold direct parallel; cases i; cases j; simp only [Matrix.of_apply,Equiv.prodCongr_apply,Equiv.refl_apply, Prod.map_apply,Equiv.apply_symm_apply,F]) -- F last might need simp
end rig
end YM.Qlocal.Quipu.Two
