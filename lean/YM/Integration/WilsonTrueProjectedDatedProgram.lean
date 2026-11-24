import YM.Integration.WilsonTrueProjectedFiledSource

/-! The independently filed finite transfer is graded along one dated physical
course. Each field at an intermediate date is used on both of its edges. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedDatedProgram
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open FormalBulk08 City Pose PhysicalNext Repeat Legato Graces Roost Org
open WilsonTrueProjectedDualHistory WilsonTrueProjectedFiledTransfer
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G) {d D : ℕ}
local notation "ι" => Letter (R.family.labels.level d)
local notation "𝓒" => R.family

def run (a : hue G) (wood : Primer.Families (𝓒)) (depth : d < D)
    (N q : ℕ) (g : ℕ → ℝ) (top : Fin (q+1) → ι → ℂ) :
    ℕ → ℕ → Fin (q+1) → ι → ℂ
  | 0,_ => top
  | n+1,j => WilsonTrueProjectedFiledGrades.layer R a wood depth N j q (g j)
      (run a wood depth N q g top n (j+1))

def income (a : hue G) (wood : Primer.Families (𝓒)) (depth : d < D)
    (N b q : ℕ) (g : ℕ → ℝ) (top : Fin (q+1) → ι → ℂ) (j : ℕ) :=
  run R a wood depth N q g top (b-j) j

theorem at_top (a : hue G) (wood : Primer.Families (𝓒)) (depth : d < D)
    (N b q : ℕ) (g : ℕ → ℝ) (top : Fin (q+1) → ι → ℂ) :
    income R a wood depth N b q g top b = top := by simp [income,run]

theorem previous (a : hue G) (wood : Primer.Families (𝓒)) (depth : d < D)
    (N b q : ℕ) (g : ℕ → ℝ) (top : Fin (q+1) → ι → ℂ) {j : ℕ} (hj : j < b) :
    income R a wood depth N b q g top j = WilsonTrueProjectedFiledGrades.layer R
      a wood depth N j q (g j) (income R a wood depth N b q g top (j+1)) := by
  unfold income
  rw [show b-j = b-(j+1)+1 by omega]
  rfl

def mesh (d m j : ℕ) : ℝ := ((𝓒).S.a j / (𝓒).S.a m)^d

theorem next_mesh (d m j : ℕ) : mesh R d m (j+1) =
    mesh R d m j / (((𝓒).S.block j).val:ℝ)^d := by
  unfold mesh
  rw [(𝓒).S.a_step, ←div_pow]
  congr 1
  ring

theorem mesh_range (d m j : ℕ) (late : m ≤ j) :
    0 < mesh R d m j ∧ mesh R d m j ≤ 1 := by
  have positive := div_pos ((𝓒).S.a_pos j) ((𝓒).S.a_pos m)
  exact ⟨pow_pos positive _, pow_le_one₀ positive.le
    ((div_le_one ((𝓒).S.a_pos m)).mpr ((𝓒).S.strictAnti.antitone late))⟩

theorem grade_price {q : ℕ} {g B : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B)
    (x : Fin (q+1) → ι → ℂ) (A : Fin (q+1) → ℝ) (u v : Fin (q+1) → ι → ℝ)
    (wage : ∀ k, ∑ b, ‖x k b‖ ≤ A k*g^k.val)
    (sale : ∀ k b, u k b+v k b ≤ B*g^(q-k.val+1)) :
    (∑ k : Fin (q+1), ∑ b, ‖x k b‖*(u k b+v k b)) ≤ (∑ k, A k)*B*g^(q+1) := by
  calc
    _ ≤ ∑ k : Fin (q+1), A k*B*g^(q+1) := by
      apply Finset.sum_le_sum
      intro k _
      calc
        _ ≤ ∑ b, ‖x k b‖*(B*g^(q-k.val+1)) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (sale k b) (norm_nonneg _)
        _ = (∑ b, ‖x k b‖)*(B*g^(q-k.val+1)) := (Finset.sum_mul ..).symm
        _ ≤ (A k*g^k.val)*(B*g^(q-k.val+1)) :=
          mul_le_mul_of_nonneg_right (wage k) (mul_nonneg hB (pow_nonneg hg _))
        _ = _ := by
          have add : k.val+(q-k.val+1)=q+1 := by have h:=k.isLt; omega
          calc
            _ = (A k*B)*(g^k.val*g^(q-k.val+1)) := by ring
            _ = _ := by rw [←pow_add,add]
    _ = _ := by simp only [Finset.sum_mul]

end YM.Integration.WilsonTrueProjectedDatedProgram
