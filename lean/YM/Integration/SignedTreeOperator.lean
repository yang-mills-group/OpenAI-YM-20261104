import YM.Integration.SignedTreeWilson
import YM.Integration.SignedTreeTensor

/-! The complete grouped observable, after native Wilson normalization,
is jointly multilinear in all original cluster fields and exterior fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedTreeOperator

open Function Filter Set Spec OPE OPE.Orbits PhysMS Wilson
open Pert.Position Maxwell Maxwell.Free MSbar.OPE RG11.Fields RG11.Grove RG11.Neighborhood
open OPETreeRemainder SignedTreeTransport
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {S : Table C.book} {n m i d : ℕ}
    (J : ℝ → PhysMS.tower S) (x : conf n) (y : Tail m) (weights : Fin n → ℕ) (H : ℕ)

/-- The true replacement moment as a linear function of the single output
field, taking values in the space of multilinear exterior responses. -/
def replacement (T : Table C.book) (J : ℝ → PhysMS.tower S) (r : ℝ) (y : Tail m) (k d : ℕ) :
    E C.labels k →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin m => E C.labels d) ℂ :=
  (SignedTreeTensor.pair (n := 1) (i := k) T J r (close y)).toLinearMap (fun _ => 0) 0

theorem replacement_apply (T : Table C.book) (r : ℝ) (k : ℕ) (z : E C.labels k)
    (w : Fin m → E C.labels d) : replacement T J r y k d z w =
      SignedTreeTensor.pair T J r (close y) (fun _ : Fin 1 => z) w := by
  have he : update (fun _ : Fin 1 => (0 : E C.labels k)) 0 z = fun _ => z := by
    funext a; fin_cases a; simp
  change SignedTreeTensor.pair T J r (close y) (update _ 0 z) w = _
  rw [he]

def tensor (T : Table C.book) (r t : ℝ) :
    MultilinearMap ℂ (fun _ : Fin n => E C.labels i)
      (MultilinearMap ℂ (fun _ : Fin m => E C.labels d) ℂ) :=
  (t : ℂ)^(∑ a,weights a) • SignedTreeTensor.pair T J r (driven t x.val y) -
    ∑ k ∈ Finset.range (H+1), (t : ℂ)^k • (replacement T J r y k d).compMultilinearMap
      (SignedTreeTensor.coefficient C.labels x k)

theorem finite_apply (hC : C.Makes) (r t : ℝ) (N p j : ℕ) (hj : j ≤ N)
    (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) :
    tensor J x y weights H (StressFlux.Matching.rounded C N p) r t v w =
      mean C N p j hj (SignedTreeWilson.grouped J x y v w weights H r t N p) := by
  rw [mean_eq hC _ _ _ _ _ (SignedTreeWilson.grouped_continuous ..), SignedTreeWilson.grouped_mean]
  simp only [tensor, _root_.sub_apply, _root_.smul_apply, _root_.sum_apply,
    LinearMap.compMultilinearMap_apply, replacement_apply, SignedTreeTensor.coefficient_apply,
    SignedTreeTensor.finite_pair, smul_eq_mul]

section Tests
variable {I A U Z : Type*} [Fintype I] [Fintype A] [NormedAddCommGroup U]
    [NormedSpace ℂ U] [FiniteDimensional ℂ U] [NormedAddCommGroup Z] [NormedSpace ℂ Z]

def cost (b : Module.Basis A ℂ U) : ℝ :=
  ∑ a : I → A, ∏ j, ‖LinearMap.toContinuousLinearMap (b.coord (a j))‖

theorem cost_nonneg (b : Module.Basis A ℂ U) : 0 ≤ cost (I := I) b :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _

/-- Off-grade basis words may be omitted when their coordinate vanishes
for the actual independent vector. -/
theorem test_bound (b : Module.Basis A ℂ U) (L : MultilinearMap ℂ (fun _ : I => U) Z)
    (v : I → U) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ u : I → A, (∏ j, b.repr (v j) (u j)) = 0 ∨ ‖L (b ∘ u)‖ ≤ B) :
    ‖L v‖ ≤ cost (I := I) b * B * ∏ j, ‖v j‖ := by
  let a := fun u : I → A => ∏ j, ‖LinearMap.toContinuousLinearMap (b.coord (u j))‖
  have hz u : 0 ≤ a u := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hc (u : I → A) : ‖∏ j, b.repr (v j) (u j)‖ ≤ a u * ∏ j, ‖v j‖ := by
    rw [norm_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun j _ => (LinearMap.toContinuousLinearMap (b.coord (u j))).le_opNorm (v j))
  rw [SignedTensor.expand b L v]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ u : I → A, a u * (B * ∏ j, ‖v j‖) := by
      apply Finset.sum_le_sum
      intro u _
      rcases h u with h0|hb
      · rw [h0, zero_smul,norm_zero]
        exact mul_nonneg (hz u) (mul_nonneg hB (Finset.prod_nonneg fun _ _ => norm_nonneg _))
      · rw [norm_smul]
        simpa only [Function.comp_def, mul_right_comm, mul_assoc, mul_left_comm] using
          (mul_le_mul (hc u) hb (norm_nonneg _) (mul_nonneg (hz u)
            (Finset.prod_nonneg fun _ _ => norm_nonneg _)))
    _ = _ := by rw [← Finset.sum_mul, ← mul_assoc]; rfl

end Tests

def atExterior (w : Fin m → E C.labels d) :
    MultilinearMap ℂ (fun _ : Fin m => E C.labels d) ℂ →ₗ[ℂ] ℂ where
  toFun L := L w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end YM.Integration.SignedTreeOperator
