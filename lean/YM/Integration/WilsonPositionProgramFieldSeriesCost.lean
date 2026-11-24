import YM.Integration.WilsonPositionProgramDatedFieldCost
import YM.Integration.WilsonPositionProgramSeriesRead

/-! Fixed-degree mass of every raised and derivative source on a common
tree. The child probes can be chosen independently on the submitted stencil. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramFieldSeriesCost
open Finset Filter Lattice Wilson RG Precision Next.Foundations
open PhysicalNext.Repeat.Legato PowerSeries Labels
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard
open WilsonCoeffUV.Power WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonPositionProgramInversionMaterial WilsonPositionProgramSeriesRead
open scoped Classical BigOperators

theorem product {I : Type} (S : Finset I) (q : ℕ) (v : I → PowerSeries ℂ) (f : I → ℝ)
    (pos : ∀ j,0≤f j) (cash : ∀ j t,t≤q → ‖coeff t (v j)‖ ≤ f j) :
    ∀ t, t≤q → ‖coeff t (∏ j∈S, v j)‖ ≤ ((q+1:ℕ):ℝ)^S.card * ∏ j∈S, f j := by
  induction S using Finset.induction_on with
  | empty =>
    intro t _
    by_cases h:t=0 <;> simp [h, coeff_one]
  | @insert j S hj old =>
    intro t ht
    rw [Finset.prod_insert hj,Finset.prod_insert hj,Finset.card_insert_of_notMem hj,coeff_mul]
    apply (norm_sum_le ..).trans
    let U : ℝ := ((q+1:ℕ):ℝ)^S.card * ∏ i∈S, f i
    have posU : 0 ≤ U := mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => pos i))
    calc ∑ u∈Finset.HasAntidiagonal.antidiagonal t, ‖coeff u.1 (v j)*coeff u.2 (∏ i∈S,v i)‖ ≤
        ∑ _∈Finset.HasAntidiagonal.antidiagonal t, f j*U := by
          apply Finset.sum_le_sum
          intro u inc
          have h := Finset.HasAntidiagonal.mem_antidiagonal.mp inc
          rw [norm_mul]
          exact mul_le_mul (cash j u.1 (by omega)) (old u.2 (by omega)) (norm_nonneg _) (pos j)
      _ = ((t+1:ℕ):ℝ)*(f j*U) := by rw [Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul]
      _ ≤ ((q+1:ℕ):ℝ)*(f j*U) := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right ht 1)
        (mul_nonneg (pos j) posU)
      _ = _ := by rw [pow_succ]; dsimp [U]; ring

variable {G : Gauge} (R : Run G) {I : Type} [Fintype I]
    (d h : I → ℕ) (fit : ∀ j,d j<h j)
local notation "F" j => R.family.labels.level (d j)
theorem native (v : (j : I) → Verse (F j)) (b : (j : I) → Volume (h j)) (q : ℕ)
    (A : I → ℝ) (pos : ∀ j,0≤A j)
    (fund : ∀ j i, i≤q → ∀ s, ‖coeff i (v j s)‖ ≤ A j) :
    ∀ a : Axes R d, ∀ t≤q, ‖coeff t (dose R d v h fit b a)‖ ≤
      ((q+1:ℕ):ℝ)^Fintype.card I * ∏ j, A j * ‖jewelBloom (fit j) (a j) (b j)‖ := by
  intro a t ht
  apply product Finset.univ q _ _ (fun j => mul_nonneg (pos j) (norm_nonneg _)) _ t ht
  intro j i hi
  rw [mul_comm,PowerSeries.coeff_C_mul,PowerSeries.coeff_map,norm_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right (fund j i hi (a j)) (norm_nonneg (jewelBloom (fit j) (a j) (b j)))

end YM.Integration.WilsonPositionProgramFieldSeriesCost
end
