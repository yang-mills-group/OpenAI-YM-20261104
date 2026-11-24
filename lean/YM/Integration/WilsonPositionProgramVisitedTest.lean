import YM.Integration.WilsonPositionProgramElectedMaster

/-! The signed cohort is summed on its actual independently visited children.
Each native four-dimensional cell fee retains its own test shape and rank. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramVisitedTest
open Function Finset Filter Lattice RG Source Precision Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open scoped Classical BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {d : I→ℕ}

theorem one {D l : ℕ} (φ : Rarity D) (x y : ℝ) (c : CellR) (A : ℝ) (budget : Amplitude φ A)
    (xpos : 0<x) (small : x≤1) (b : Vote D) :
    (∑ z ∈ VisitsT φ x y c, |drumB l x| * ‖b (wheelC x y z φ.ψ c)‖) ≤
      BasePrice l φ x y * (‖b‖*A) := by
  refine (Finset.sum_le_sum (g:=fun _ => |drumB l x| * (‖b‖*A)) (fun z _ =>
    mul_le_mul_of_nonneg_left ((b.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (amplitudes_bound x y budget xpos.le small c z) (norm_nonneg _))) (abs_nonneg _))).trans ?_
  exact expanse φ x y c xpos small l (‖b‖*A) (mul_nonneg (norm_nonneg _) budget.1)

theorem faces (l : I→ℕ) (φ : (i:I)→Rarity (d i)) (x : ℝ) (y : I→ℝ)
    (c : I→ CellR) (A : I→ℝ) (budget : ∀ i,Amplitude (φ i) (A i)) (xpos : 0<x)
    (small : x≤1) (b : (i:I)→Vote (d i)) (S : Finset (I → Cover))
    (visits : S⊆Fintype.piFinset (fun i=>VisitsT (φ i) x (y i) (c i))) :
    (∑ z ∈ S, ∏ i, |drumB (l i) x| * ‖b i (wheelC x (y i) (z i) (φ i).ψ (c i))‖) ≤
      ∏ i, BasePrice (l i) (φ i) x (y i) * (‖b i‖*A i) := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg visits (fun z _ _ =>
    Finset.prod_nonneg (fun i _=>mul_nonneg (abs_nonneg _) (norm_nonneg _)))).trans ?_
  rw [←Finset.prod_univ_sum (fun i=> VisitsT (φ i) x (y i) (c i))
    (fun i z=>|drumB (l i) x| * ‖b i (wheelC x (y i) z (φ i).ψ (c i))‖)]
  exact Finset.prod_le_prod (fun i _=>Finset.sum_nonneg fun z _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
    (fun i _=>one (l:=l i) (φ i) x (y i) (c i) (A i) (budget i) xpos small (b i))

end YM.Integration.WilsonPositionProgramVisitedTest
end
