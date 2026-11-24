import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import YM.MS.Book.Triang
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace PhysicalMatching.H7StandaloneIntegratedTriangularTestKernel
open Function Filter Set
open scoped Topology BigOperators Classical
def RowPrice (clock : ℝ → ℝ) (p : ℕ) (actual : ℝ → ℂ) (filed : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
    ‖actual r - ∑ k : Fin (p+1), (clock r : ℂ)^k.val * filed k.val‖ ≤ C * |clock r|^(p+1)

private theorem rangeIic (p : ℕ) : Finset.range (p+1) = Finset.Iic p := by
  ext i
  simp [Nat.lt_succ_iff]

private theorem finIic (p : ℕ) (f : ℕ → ℂ) :
    (∑ i : Fin (p+1), f i.val) = ∑ i ∈ Finset.Iic p, f i := by
  rw [Fin.sum_univ_eq_sum_range, rangeIic]

theorem triangularCrop (t : ℂ) (p : ℕ) (c : ℕ → ℕ → ℂ) :
    (∑ j : Fin (p+1), t^j.val * ∑ i : Fin (p-j.val+1), t^i.val * c j.val i.val) =
      ∑ k : Fin (p+1), t^k.val * ∑ j : Fin (k.val+1), c j.val (k.val-j.val) := by
  classical
  let K (j i : ℕ) := if j+i ≤ p then t^(j+i) * c j i else 0
  have cut (j i : ℕ) (over : p < j+i) : K j i = 0 := by simp [K,Nat.not_le.mpr over]
  have row (j : ℕ) (hj : j ≤ p) :
      t^j * (∑ i ∈ Finset.Iic (p-j), t^i * c j i) = ∑ i ∈ Finset.Iic p, K j i := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ i ∈ Finset.Iic (p-j), K j i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_Iic.mp hi
        simp [K, show j+i ≤ p by omega,pow_add,mul_assoc]
      _ = _ := Finset.sum_subset (Finset.Iic_subset_Iic.mpr (Nat.sub_le p j)) (by
        intro i hi hn
        apply cut
        simp only [Finset.mem_Iic] at hn
        omega)
  have diagonal (k : ℕ) (hk : k ≤ p) :
      (∑ z ∈ Finset.antidiagonal k, K z.1 z.2) = t^k * ∑ j ∈ Finset.Iic k, c j (k-j) := by
    calc
      _ = ∑ z ∈ Finset.antidiagonal k, t^k * c z.1 z.2 := by
        apply Finset.sum_congr rfl
        intro z hz
        simp [K,Finset.mem_antidiagonal.mp hz,hk]
      _ = t^k * ∑ z ∈ Finset.antidiagonal k, c z.1 z.2 := (Finset.mul_sum ..).symm
      _ = _ := by rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := c),rangeIic]
  calc
    _ = ∑ j ∈ Finset.Iic p, t^j * ∑ i ∈ Finset.Iic (p-j), t^i * c j i := by
      rw [← finIic p (fun j => t^j * ∑ i ∈ Finset.Iic (p-j), t^i * c j i)]
      apply Finset.sum_congr rfl
      intro j _
      rw [finIic (p-j.val) (fun i => t^i * c j.val i)]
    _ = ∑ j ∈ Finset.Iic p, ∑ i ∈ Finset.Iic p, K j i :=
      Finset.sum_congr rfl fun j hj => row j (Finset.mem_Iic.mp hj)
    _ = ∑ k ∈ Finset.Iic p, ∑ z ∈ Finset.antidiagonal k, K z.1 z.2 :=
      YM.MS.Book.Program.price K p cut
    _ = ∑ k ∈ Finset.Iic p, t^k * ∑ j ∈ Finset.Iic k, c j (k-j) :=
      Finset.sum_congr rfl fun k hk => diagonal k (Finset.mem_Iic.mp hk)
    _ = _ := by
      rw [← finIic p (fun k => t^k * ∑ j ∈ Finset.Iic k, c j (k-j))]
      apply Finset.sum_congr rfl
      intro k _
      rw [finIic k.val (fun j => c j (k.val-j))]

theorem integratedInsertion (clock : ℝ → ℝ) (a : ℝ → ℂ) (slots : ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℂ)
    (moving : ∀ p, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖a r - ∑ j : Fin (p+1), (clock r : ℂ)^j.val * slots j.val r‖ ≤ K*|clock r|^(p+1))
    (fixed : ∀ j q, RowPrice clock q (slots j) (c j)) (p : ℕ) :
    RowPrice clock p a (fun k => ∑ j : Fin (k+1), c j.val (k-j.val)) := by
  classical
  obtain ⟨K,hK,hmove⟩ := moving p
  choose B hB hfixed using fun j : Fin (p+1) => fixed j.val (p-j.val)
  refine ⟨K + ∑ j, B j,add_nonneg hK (Finset.sum_nonneg fun j _ => hB j),?_⟩
  filter_upwards [hmove,Filter.eventually_all.2 hfixed] with r hm hf
  let t := (clock r : ℂ)
  let v := ∑ j : Fin (p+1), t^j.val * slots j.val r
  let f := fun j : Fin (p+1) => ∑ i : Fin (p-j.val+1), t^i.val * c j.val i.val
  have delta : ‖v - ∑ j : Fin (p+1), t^j.val * f j‖ ≤ (∑ j, B j)*|clock r|^(p+1) := by
    change ‖(∑ j : Fin (p+1), t^j.val * slots j.val r) - ∑ j : Fin (p+1), t^j.val * f j‖ ≤ _
    rw [← Finset.sum_sub_distrib,Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← mul_sub,norm_mul,norm_pow,show ‖t‖ = |clock r| by simp [t,Real.norm_eq_abs]]
    have jp := j.isLt
    calc
      _ ≤ |clock r|^j.val * (B j * |clock r|^(p-j.val+1)) :=
        mul_le_mul_of_nonneg_left (hf j) (pow_nonneg (abs_nonneg _) _)
      _ = B j * |clock r|^(p+1) := by
        rw [mul_left_comm,← pow_add,show j.val+(p-j.val+1) = p+1 by omega]
  rw [← triangularCrop t p c]
  change ‖a r - ∑ j : Fin (p+1), t^j.val * f j‖ ≤ _
  have triangle : ‖a r - ∑ j : Fin (p+1), t^j.val * f j‖ ≤
      ‖a r - v‖ + ‖v - ∑ j : Fin (p+1), t^j.val * f j‖ := by
    simpa only [dist_eq_norm] using dist_triangle (a r) v (∑ j : Fin (p+1), t^j.val * f j)
  exact triangle.trans ((add_le_add hm delta).trans_eq (add_mul ..).symm)

theorem coordinateTail (clock : ℝ → ℝ) (u : ℝ → Fin 4 → ℂ) (U : ℕ → Fin 4 → ℂ)
    (columns : Fin 4 → ℝ → ℂ)
    (price : ∀ p, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i,
      ‖u r i - ∑ j : Fin (p+1), (clock r : ℂ)^j.val * U j.val i‖ ≤ K * |clock r|^(p+1))
    (bounded : ∀ i, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ‖columns i r‖ ≤ D)
    (p : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖(∑ i, u r i * columns i r) - ∑ j : Fin (p+1), (clock r : ℂ)^j.val *
        ∑ i, U j.val i * columns i r‖ ≤ K * |clock r|^(p+1) := by
  classical
  obtain ⟨B,hB,hprice⟩ := price p
  choose D hD hbound using bounded
  refine ⟨B*(∑ i,D i),mul_nonneg hB (Finset.sum_nonneg fun i _ => hD i),?_⟩
  filter_upwards [hprice,Filter.eventually_all.2 hbound] with r hr hd
  let t := (clock r : ℂ)
  have eqn : (∑ i,u r i * columns i r) - ∑ j : Fin (p+1), t^j.val * ∑ i,U j.val i * columns i r =
      ∑ i, (u r i - ∑ j : Fin (p+1),t^j.val * U j.val i) * columns i r := by
    simp only [sub_mul,Finset.sum_sub_distrib,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (p+1)))) (t := (Finset.univ : Finset (Fin 4)))]
  rw [eqn]
  calc
    _ ≤ ∑ i, (B * |clock r|^(p+1)) * D i := (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => by rw [norm_mul]; exact mul_le_mul (hr i) (hd i) (norm_nonneg _) (mul_nonneg hB (pow_nonneg (abs_nonneg _) _)))
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem pricedColumnBound {clock : ℝ → ℝ} (small : ∀ᶠ r : ℝ in 𝓝[>] 0, |clock r| ≤ 1)
    {a : ℝ → ℂ} {c : ℕ → ℂ} (h : RowPrice clock 0 a c) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ‖a r‖ ≤ D := by
  obtain ⟨B,hB,hpaid⟩ := h
  refine ⟨B+‖c 0‖,add_nonneg hB (norm_nonneg _),?_⟩
  filter_upwards [hpaid,small] with r hr hs
  have hc : ‖a r - c 0‖ ≤ B := (by simpa using hr : ‖a r - c 0‖ ≤ B * |clock r|).trans
    (by simpa using mul_le_mul_of_nonneg_left hs hB)
  exact (norm_le_norm_sub_add _ _).trans (add_le_add hc le_rfl)

end PhysicalMatching.H7StandaloneIntegratedTriangularTestKernel
