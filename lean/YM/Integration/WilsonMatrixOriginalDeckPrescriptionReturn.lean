import YM.Integration.WilsonMatrixOriginalDeckPrescriptionFields

/-! The full two-clock source transfer at every fine gauge, actual site and genuine perturbative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionReturn
open PhysicalNext.Repeat.Legato Finset Lattice Wilson RG MS MS.Menus MS.Local.Physical
open WilsonMatrixOriginalDeckPrescription WilsonMatrixOriginalDeckPrescriptionFields WilsonMatrixOriginalDeckPrescriptionSeries
open scoped Classical BigOperators Matrix
variable {G:Gauge}{B:Deck G} (R:Run G) (Q:MS.Land.Prescription B) (h:ℕ)
local notation "I"=>Glyph B h

private theorem row (μ:ℝ)(k N p:ℕ)(o:Site (R.family.side N p))(U:Config G (R.family.side N p)):
    field R Q h μ k N p o U=raw R h N p o U ᵥ* fees Q h μ k:=by
  funext a;rw [observed,Matrix.vecMul_apply_eq_sum];apply sum_congr rfl;intro j _;exact mul_comm _ _

private theorem vec_sum {m:ℕ}(v:I→ℂ)(A:Fin m→Matrix I I ℂ):
    v ᵥ* (∑j,A j)=∑j,v ᵥ* A j:=by
  funext i;simp only [Matrix.vecMul_apply_eq_sum,Matrix.sum_apply,Finset.sum_apply,Finset.mul_sum]
  exact Finset.sum_comm

/-- Every true prescribed far-clock observable is exactly reproduced at the near clock by its entire causal matrix. -/
theorem measured (μ ν:ℝ)(k N p:ℕ)(o:Site (R.family.side N p))(U:Config G (R.family.side N p)):
    field R Q h ν k N p o U=∑j:Fin (k+1),field R Q h μ (k-j.val) N p o U ᵥ* trial Q h μ ν j.val:=by
  rw [row,←WilsonMatrixOriginalDeckPrescriptionSeries.measured Q h μ ν k,vec_sum]
  apply sum_congr rfl
  intro j _
  rw [row,Matrix.vecMul_vecMul]

theorem born (μ ν:ℝ)(N p:ℕ)(o:Site (R.family.side N p))(U:Config G (R.family.side N p)):
    field R Q h ν 0 N p o U=field R Q h μ 0 N p o U ᵥ* trial Q h μ ν 0:=by
  simpa using measured R Q h μ ν 0 N p o U

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionReturn
