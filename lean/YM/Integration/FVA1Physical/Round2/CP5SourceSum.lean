import YM.QuadraticLocal.Class.Foundry

/-! Read an independently supplied scalar field in every singleton row.
The identified sum is the donor's full pre-mask logarithm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Finset Lattice YM.Wilson RG Marker QuadraticLocal QuadraticLocal.Earn
open scoped Classical BigOperators
variable {G:Gauge} {I α:Type} [Fintype I] [DecidableEq I] {n:Side}

theorem identified_rows (J:Census I) (P:Passport n I) (count:I→ℕ)
    (X:(Σ i,Fin (count i))→Row P J G α) (mode:∀ p,(X p).mode=J.fire p.1)
    (g:ℝ) (t:α) (U:Config G n) (field:I→ℂ)
    (read:∀ i,field i=∑ j:Fin (count i),(X ⟨i,j⟩).nominal g t U) :
    Spill.Foundry.uncut X g t U = ∑ i,Poly.send (J.fire i) (field i) := by
  ext s
  rw [Spill.Foundry.uncut,tsum_fintype,Poly.part_sum,Poly.part_sum,Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  simp_rw [Spill.raw,Poly.part_send,mode]
  by_cases h:s=J.fire i
  · simp only [h,ite_true]
    exact (read i).symm
  · simp [h]

end YM.Integration.FVA1Physical.Round2.CP5
