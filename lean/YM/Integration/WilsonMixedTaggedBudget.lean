import YM.Integration.WilsonMixedTaggedEntries

/-! Charging one split mode per input monomial preserves the entire original
site sum. The amplifier acts before the field and root are chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedBudget
open Finset Function Set Marker RG05Readout.Many Lattice RG MergeProof Accent
open Push GridApprox.Nil Ac AbsoluteSums WilsonMixedTaggedEntries
open scoped BigOperators Classical

variable {V I Y : Type*} [DecidableEq V] [Fintype V] {B : Census V}
local notation "Bₜ" => Lift B (Prod.fst : V × Bool → V)
variable {n : Side} {w : V → ℝ} {X : I → Support n} {b : ℕ} {e t : ℝ}

theorem loci (c : ℂ) {P : Y → Poly B} (h:Loci w P t) :
    Loci (w ∘ Prod.fst) (fun U=>pack c (P U)) (‖c‖*t) := by
  obtain ⟨a,ha,hP,hs⟩ := h
  let u (y:(Bₜ).Mode) := if y=charged (base y) then ‖c‖*a (base y) else 0
  refine ⟨u,fun y=>?_,fun U y=>?_,?_⟩
  · unfold u
    split
    · exact mul_nonneg (norm_nonneg _) (ha _)
    · rfl
  · rw [part_pack]
    unfold u
    split
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hP U _) (norm_nonneg _)
    · rw [norm_zero]
  apply le_trans _ (mul_le_mul_of_nonneg_left hs (norm_nonneg c))
  apply le_of_eq
  let img := (univ : Finset B.Mode).image charged
  let f (y:(Bₜ).Mode) := Poly.toll (w ∘ Prod.fst) y * u y
  change ∑ y, f y = ‖c‖ * ∑ y, Poly.toll w y * a y
  rw [← Finset.sum_subset (Finset.subset_univ img),show img=(Finset.univ:Finset B.Mode).image charged from rfl,Finset.sum_image]
  · rw [Finset.mul_sum]
    apply sum_congr rfl
    intro x _
    simp [f,u,toll_charged,mul_left_comm]
  · intro x _ y _ he
    simpa using congrArg base he
  · intro y _ hy
    have off : y≠charged (base y) := fun h=>hy (h ▸ mem_image_of_mem charged (mem_univ _))
    simp [f,u,off]

theorem towed (c : ℂ) {P : I → Y → Poly B} (h : Towed w X P b e t) :
    Towed (w ∘ Prod.fst) X (fun i U=>pack c (P i U)) b e (‖c‖*t) := by
  obtain ⟨a,sa,ha,head⟩ := h
  refine ⟨fun i=>‖c‖*a i,sa.mul_left _,fun x=>?_,fun i=>loci c (head i)⟩
  convert budget_scale (norm_nonneg c) (ha x) using 1
  ext j
  split_ifs <;> ring

theorem unit {δ : ℝ} (hd : 0 < δ) {P : I → Y → Poly B}
    (h : Towed w X P b e δ) :
    Towed (w ∘ Prod.fst) X (fun i U=>pack (δ:ℂ)⁻¹ (P i U)) b e 1 := by
  simpa [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd,hd.ne'] using
    towed (δ:ℂ)⁻¹ h

end YM.Integration.WilsonMixedTaggedBudget
