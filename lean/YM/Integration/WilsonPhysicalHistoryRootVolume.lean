import YM.Extra.MULTISOURCE_BOUNDS.Root
import YM.Marker.Weight

/-! Finite-volume admission of exactly the filed hard majorant, including
its quiet coordinate. The subsequent fiscal tests use the sharper root bill. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryRootVolume
open Finset Lattice Wilson RG Marker Extra.Multi
open scoped Classical BigOperators
variable {V I : Type*} [DecidableEq V] {G : Gauge} {n : Side}
  (C : Census V) (D : I → ForcedAddress G n) (majorant : I → Poly C)
  (weights : V → ℝ) (positive : ∀ v, 0 < weights v)
  (site : I × C.Mode → Site n) {B : ℕ} {A bound : ℝ}

private theorem entire {K : Type*} {place : K → Site n} {crest : K → Support n}
    {fee : K → ℝ} (nonneg : ∀ i, 0 ≤ fee i)
    (paid : Rooted (fun i => {place i}) crest B A fee bound) :
    SumBudget (fun i => Real.exp (A * coverNumber B (crest i)) * fee i)
      ((Fintype.card (Site n) : ℝ) * bound) := by
  classical
  apply Budget.certify (fun i => mul_nonneg (Real.exp_pos _).le (nonneg i))
  intro entries
  let charge (x : Site n) (i : K) :=
    if x ∈ ({place i} : Finset (Site n)) then Real.exp (A * coverNumber B (crest i)) * fee i else 0
  calc
    _ = ∑ i ∈ entries, ∑ x, charge x i := by simp [charge]
    _ = ∑ x, ∑ i ∈ entries, charge x i := sum_comm
    _ ≤ ∑ _x : Site n, bound := sum_le_sum fun x _ => by
      simpa [charge] using Budget.cap (paid x) entries
    _ = _ := by simp

theorem tabulate {J : Type*} [Fintype J] (fee : I × J → ℝ) (nonneg : ∀ i, 0 ≤ fee i)
    (all : SumBudget (fun j => Real.exp (A * coverNumber B (D j.1).support) * fee j) bound) :
    Ac.Hit (fun i => (D i).support) B (fun i => ∑ s, fee (i,s)) A bound := by
  classical
  intro x
  apply Budget.certify
  · intro i
    split
    · exact mul_nonneg (sum_nonneg fun s _ => nonneg (i,s)) (Real.exp_pos _).le
    · exact le_rfl
  intro entries
  calc
    _ ≤ ∑ i ∈ entries, ∑ s : J, Real.exp (A * coverNumber B (D i).support) * fee (i,s) := by
      apply sum_le_sum
      intro i _
      split
      · rw [← mul_sum, mul_comm]
      · exact sum_nonneg fun s _ => mul_nonneg (Real.exp_pos _).le (nonneg (i,s))
    _ = ∑ j ∈ entries ×ˢ (univ : Finset J),
        Real.exp (A * coverNumber B (D j.1).support) * fee j := by rw [sum_product]
    _ ≤ _ := Budget.cap all _

include positive in
theorem admission
    (paid : Rooted (fun j => {site j}) (fun j => (D j.1).support) B A
      (fun j => Poly.toll weights j.2 * ‖(majorant j.1).part j.2‖) bound) :
    Ac.Hit (fun i => (D i).support) B (fun i => Poly.price weights (majorant i)) A
      ((Fintype.card (Site n) : ℝ) * bound) :=
  let nonneg := fun i : I × C.Mode => mul_nonneg (Poly.worth positive i.2).le (norm_nonneg ((majorant i.1).part i.2))
  tabulate D _ nonneg (entire nonneg paid)

end YM.Integration.WilsonPhysicalHistoryRootVolume
end

