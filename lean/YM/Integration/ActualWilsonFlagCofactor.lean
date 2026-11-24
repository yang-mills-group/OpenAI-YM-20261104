import YM.Integration.ActualWilsonJoinedCofactor

/-! Count only genuine flags in a surviving original punctured Wilson packet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonFlagCofactor
open Finset Lattice RG Wilson Extra.Histories ActualWilsonPacketSplit ActualWilsonJoinedCofactor
open scoped BigOperators Classical
variable {G : Gauge} {n : Side}

theorem flag_count (W : Rep G n) {S Z : Support n} (hZ : Z ⊆ S) {J : Finset ℕ}
    {U : Config G n} (h : permits W S Z J U) : J.card + Z.card ≤ (flags W.p.threshold U).card := by
  have hp : (J : Set ℕ).PairwiseDisjoint (inventory W) :=
    fun i hi j hj hij => (h.1 hi hj hij).mono
      (W.activities.forced i).inventory_sup (W.activities.forced j).inventory_sup
  have hj : J.card ≤ (J.biUnion (inventory W)).card := by
    rw [Finset.card_biUnion hp]
    calc
      _ = ∑ _ ∈ J, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => card_pos.mpr (W.activities.forced j).inventory_ne
  have hd : Disjoint Z (J.biUnion (inventory W)) := by
    apply Finset.disjoint_left.2
    intro x hx hy
    obtain ⟨j,hj,hy⟩ := mem_biUnion.1 hy
    exact Finset.disjoint_left.1 (h.2.1 j hj) (hZ hx) ((W.activities.forced j).inventory_sup hy)
  rw [← h.2.2,card_union_of_disjoint hd]
  omega

theorem truncated (W : Rep G n) (k : ℕ) (U : Config G n) :
    dressed W k U = ∑' J : Finset ℕ,
      if J.card + (inventory W k).card ≤ (flags W.p.threshold U).card then
        waiting W (scopes W k) (inventory W k) J U else 0 := by
  rw [dressed_eq]
  apply tsum_congr
  intro J
  by_cases h : J.card + (inventory W k).card ≤ (flags W.p.threshold U).card
  · rw [if_pos h]
  rw [if_neg h,waiting,if_neg (fun p => h (flag_count W (W.activities.forced k).inventory_sup p))]

theorem filled (W : Rep G n) (k : ℕ) (U : Config G n) (h : inventory W k = flags W.p.threshold U) :
    dressed W k U = 1 := by
  rw [dressed_eq,tsum_eq_single (∅ : Finset ℕ)]
  · have h0 : permits W (scopes W k) (inventory W k) ∅ U := by simpa [permits] using h
    simp [waiting,h0]
  intro J hJ
  apply if_neg
  intro p
  have hc : J.card + (inventory W k).card ≤ (flags W.p.threshold U).card :=
    flag_count W (W.activities.forced k).inventory_sup p
  rw [h] at hc
  exact hJ (Finset.card_eq_zero.mp (by omega))

theorem excluded (W : Rep G n) (k : ℕ) (U : Config G n)
    (h : ¬inventory W k ⊆ flags W.p.threshold U) : dressed W k U = 0 := by
  rw [dressed_eq]
  apply (tsum_congr (g := fun _ : Finset ℕ => (0:ℂ)) ?_).trans tsum_zero
  intro J
  apply if_neg
  intro p
  apply h
  rw [←p.2.2]
  exact Finset.subset_union_left

theorem one_flag (W : Rep G n) (k : ℕ) (U : Config G n) (h : (flags W.p.threshold U).card ≤ 1) :
    dressed W k U = if inventory W k = flags W.p.threshold U then 1 else 0 := by
  by_cases p : inventory W k = flags W.p.threshold U
  · rw [if_pos p,filled W k U p]
  rw [if_neg p]
  apply excluded
  intro hs
  have hz : 0 < (inventory W k).card := Finset.card_pos.mpr (W.activities.forced k).inventory_ne
  exact p (Finset.eq_of_subset_of_card_le hs (by omega))

end YM.Integration.ActualWilsonFlagCofactor
