import YM.Integration.WilsonPositionProgramGaussianRadialStock

/-! Finite normalized Wilson response with one common graded seam times the genuine Gaussian cofactor. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramGaussianDriverExpense
open Function Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange Next.SectorChange.Gaussian PertExtension.Series Multi Marker Comparison.RG02
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Order
open WilsonPositionProgramGaussianRoute WilsonPositionProgramGaussianEnvelope WilsonPositionProgramFiledGaussianChange
open WilsonPositionProgramFiledGaussianPrice WilsonPositionProgramGaussianRadialStock
open scoped BigOperators Classical

theorem scaled {I V:Type}[DecidableEq V][Fintype I][DecidableEq I]{R:Census V}
    (Q:Matrix I I ℝ)(hQ:Q.IsSymm)(m:I→ℝ)(p q:Hot R→Normal.poly I)(s:R.Mode)
    (δ:ℝ)(e:Hot R→ℝ)(E:Hot R→Normal.poly I)(u:List (Hot R)):
    expense Q hQ m p q s (fun i=>δ*e i) E u = δ*expense Q hQ m p q s e E u := by
  induction u with
  | nil=>simp [expense]
  | cons i tail ih=>simp only [expense,ih,mul_add,mul_assoc]

variable {G:Gauge}{c f:Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(tag:S.Choices)
  {V:Type}[DecidableEq V][Fintype V]{R:Census V}

theorem signed (W Y:Bulk.Colors R G f)(A:fieldDir G c 1){d r:ℕ}(retained:d≤r)
    (s:R.Mode)(live:s≠R.quiet){δ:ℝ}(hδ:0≤δ)
    (e:Hot (Board R r)→ℝ)(he:∀i,0≤e i)(k:Hot (Board R r)→ℕ)
    (draw:∀i z,‖Cloud.paint z (drivers K F tag Y A r i-drivers K F tag W A r i)‖≤
      (δ*e i)*(1+‖z‖)^(k i)):
    ‖(d.factorial:ℂ)*((observe R r (logMarked (Bulk.Fk K F tag Y A r)) d).part s-
      (observe R r (logMarked (Bulk.Fk K F tag W A r)) d).part s)‖ ≤
    δ*expense (K.covariance F tag) (K.symm F tag) 0 (drivers K F tag W A r) (drivers K F tag Y A r)
      (Join.pair s (pick r d)) (fun i=>2*e i) (fun i=>radial (k i)) univ.toList := by
  rw [←scaled]
  apply WilsonPositionProgramFiledGaussianPrice.original K F tag W Y A retained s live 0
  intro i z
  have sale:=centered (Join.pair s (pick r d)) i (drivers K F tag Y A r i-drivers K F tag W A r i)
    (δ*e i) (mul_nonneg hδ (he i)) (k i) (draw i) z
  rw [mul_left_comm 2 δ (e i)] at sale
  exact sale

end YM.Integration.WilsonPositionProgramGaussianDriverExpense
end
