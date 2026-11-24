import YM.Comparison.RG02.Algebra.Markers

/-! Relative error of the marked density reconstructed from independent connected Wilson coefficients. The empty coefficient is fixed by the physical vacuum normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Marker Extra.Trajectories Finset
open scoped Classical BigOperators

variable {W : Type} [DecidableEq W] [Fintype W] {C : Census W}

/-- Install all nonempty connected coefficients, with the normalization of a logarithm. -/
def wilsonLogTable (C : Census W) (entry : C.Mode → ℂ) : Poly C :=
  Poly.inject fun T => if T = C.quiet then 0 else entry T

private theorem exponential_tail (weight : W → ℝ) (hw : ∀ l, 0 < weight l)
    (x : Poly C) (zero : x.part C.quiet = 0) :
    Poly.price weight (Poly.pass x - 1) ≤ Real.exp (Poly.price weight x) - 1 := by
  have equal : Poly.price weight (Poly.pass x - 1) + 1 = Poly.price weight (Poly.pass x) := by
    let f := fun T : C.Mode => Poly.toll weight T * ‖(Poly.pass x - 1).part T‖
    let h := fun T : C.Mode => Poly.toll weight T * ‖(Poly.pass x).part T‖
    change (∑ T, f T) + 1 = ∑ T, h T
    rw [← sum_erase_add _ f (mem_univ C.quiet), ← sum_erase_add _ h (mem_univ C.quiet)]
    have fq : f C.quiet = 0 := by simp [f, part_sub, Poly.pass_part x zero, Poly.one_part]
    have hq : h C.quiet = 1 := by simp [h, Poly.pass_part x zero]
    rw [fq, hq, add_zero]
    congr 1
    apply sum_congr rfl
    intro T mem
    simp only [f, h, part_sub, Poly.one_part, if_neg (ne_of_mem_erase mem), sub_zero]
  linarith only [equal, Poly.pass_budget hw x]

theorem wilson_density_error (weight : W → ℝ) (hw : ∀ l, 0 < weight l)
    (v : Poly C) (normed : v.part C.quiet = 1) (entry : C.Mode → ℂ) (cost : C.Mode → ℝ)
    (est : ∀ T, T ≠ C.quiet → Poly.toll weight T * ‖(connected v).part T - entry T‖ ≤ cost T) :
    let Z := wilsonLogTable C entry
    let bill := ∑ T ∈ (univ.erase C.quiet), cost T
    let relative := Poly.pass (connected v - Z) - 1
    Poly.price weight (connected v - Z) ≤ bill ∧
    Poly.price weight relative ≤ Real.exp bill - 1 ∧
    v - Poly.pass Z = Poly.pass Z * relative ∧
    Poly.price weight (v - Poly.pass Z) ≤ Real.exp (Poly.price weight Z) * (Real.exp bill - 1) := by
  intro Z bill relative
  have z0 : Z.part C.quiet = 0 := by simp [Z, wilsonLogTable, Poly.inject, Poly.part]
  have v0 := connected_quiet normed
  have err0 : (connected v - Z).part C.quiet = 0 := by rw [part_sub, v0, z0, sub_self]
  have paid : Poly.price weight (connected v - Z) ≤ bill := by
    unfold Poly.price
    rw [← sum_erase_add _ _ (mem_univ C.quiet), err0, norm_zero, mul_zero, add_zero]
    apply sum_le_sum
    intro T hT
    have ne := ne_of_mem_erase hT
    change Poly.toll weight T * ‖(connected v).part T - (if T = C.quiet then 0 else entry T)‖ ≤ cost T
    simpa only [if_neg ne] using est T ne
  have rel : Poly.price weight relative ≤ Real.exp bill - 1 :=
    (exponential_tail weight hw _ err0).trans (sub_le_sub_right (Real.exp_monotone paid) 1)
  have identity : v - Poly.pass Z = Poly.pass Z * relative := by
    have sum : Z + (connected v - Z) = connected v := by abel
    have h := pass_add z0 err0
    rw [sum, pass_connected normed] at h
    change v - Poly.pass Z = Poly.pass Z * (Poly.pass (connected v - Z) - 1)
    rw [mul_sub, mul_one]
    exact congrArg (fun x => x - Poly.pass Z) h
  refine ⟨paid, rel, identity, ?_⟩
  rw [identity]
  exact (Poly.multiplication hw _ _).trans (mul_le_mul (Poly.pass_budget hw _) rel
    (Poly.nonnegative hw _) (Real.exp_pos _).le)

end YM.Integration.FVA1Physical.Round2.CP5
