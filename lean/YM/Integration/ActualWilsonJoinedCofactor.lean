import YM.Integration.ActualWilsonPacketSplit
import YM.Integration.ActualWilsonInventorySlot

/-! The untouched part of an original Wilson packet is the native cofactor
of the actual slot with its joined support and combined inventory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonJoinedCofactor
open Finset Lattice RG Wilson Extra.Histories ActualWilsonPacketSplit
open scoped BigOperators Classical
variable {G : Gauge} {n : Side}

def permits (W : Rep G n) (S Z : Support n) (J : Finset ℕ) (U : Config G n) :=
  (J : Set ℕ).Pairwise (fun i j => Disjoint (scopes W i) (scopes W j)) ∧
  (∀ j ∈ J, Disjoint S (scopes W j)) ∧ Z ∪ J.biUnion (inventory W) = flags W.p.threshold U

def waiting (W : Rep G n) (S Z : Support n) (J : Finset ℕ) (U : Config G n) : ℂ :=
  if permits W S Z J U then ∏ j ∈ J, (W.activities.K j U : ℂ) else 0

theorem attach (W : Rep G n) (k : ℕ) (J : Finset ℕ) (hk : k ∉ J) (U : Config G n) :
    W.activities.admissible W.p U (insert k J) ↔ permits W (scopes W k) (inventory W k) J U := by
  constructor
  · rintro ⟨h,hcover⟩
    refine ⟨fun _ hi _ hj hij => h (mem_insert_of_mem hi) (mem_insert_of_mem hj) hij,
      ?_,?_⟩
    · intro j hj
      exact h (mem_insert_self ..) (mem_insert_of_mem hj) (fun e => hk (e ▸ hj))
    simpa only [biUnion_insert] using hcover
  rintro ⟨hJ,hcross,hcover⟩
  refine ⟨?_,by simpa only [biUnion_insert] using hcover⟩
  intro i hi j hj hij
  rcases mem_insert.1 hi with hik|hi'
  · subst i
    exact hcross j ((mem_insert.1 hj).resolve_left (Ne.symm hij))
  rcases mem_insert.1 hj with hjk|hj'
  · subst j
    exact (hcross i hi').symm
  exact hJ hi' hj' hij

def flip (k : ℕ) (J : Finset ℕ) := if k ∈ J then J.erase k else insert k J

theorem involution (k : ℕ) (J : Finset ℕ) : flip k (flip k J) = J := by
  by_cases hk : k ∈ J <;> simp [flip,hk]

def switch (k : ℕ) : Finset ℕ ≃ Finset ℕ where
  toFun := flip k
  invFun := flip k
  left_inv := involution k
  right_inv := involution k

theorem coat_eq (W : Rep G n) (k : ℕ) (J : Finset ℕ) (U : Config G n) :
    coat W k (flip k J) U = waiting W (scopes W k) (inventory W k) J U := by
  by_cases hk : k ∈ J
  · have hn : ¬permits W (scopes W k) (inventory W k) J U := by
      intro h
      obtain ⟨x,hx⟩ := (W.activities.forced k).inventory_ne.mono (W.activities.forced k).inventory_sup
      exact Finset.disjoint_left.1 (h.2.1 k hk) hx hx
    simp [coat,flip,waiting,hk,hn]
  have ha := attach W k J hk U
  simp only [flip,hk,if_false,coat,mem_insert_self,true_and,waiting,ha,Finset.erase_insert hk]

theorem dressed_eq (W : Rep G n) (k : ℕ) (U : Config G n) :
    dressed W k U = ∑' J : Finset ℕ, waiting W (scopes W k) (inventory W k) J U := by
  change (∑' s, coat W k s U) = _
  rw [← (switch k).tsum_eq (fun s => coat W k s U)]
  exact tsum_congr fun J => coat_eq W k J U

theorem inventory_subset (W : Rep G n) (Y : Support n) (I : Finset ℕ) :
    I.biUnion (inventory W) ⊆ joined W Y I := by
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.1 hx
  exact mem_union_right _ (mem_biUnion.2 ⟨i,hi,(W.activities.forced i).inventory_sup hx⟩)

/-- The entire original flag test of the joined signed slot follows from
the disjoint untreated partners and complete coverage. -/
theorem eligible (W : Rep G n) (S Z : Support n) (hZ : Z ⊆ S) (J : Finset ℕ) (U : Config G n)
    (h : permits W S Z J U) : S ∩ flags W.p.threshold U = Z := by
  ext x
  rw [←h.2.2]
  constructor
  · intro hx
    rcases mem_inter.1 hx with ⟨hS,hF⟩
    rcases mem_union.1 hF with hZ|hJ
    · exact hZ
    obtain ⟨j,hj,hx⟩ := mem_biUnion.1 hJ
    exact (Finset.disjoint_left.1 (h.2.1 j hj) hS ((W.activities.forced j).inventory_sup hx)).elim
  intro hx
  exact mem_inter.2 ⟨hZ hx,mem_union_left _ hx⟩

/-- Original signed packet product equals the touching row multiplied by its
true native cofactor kernel, including the exact local slot indicator. -/
theorem split (W : Rep G n) (Y : Support n) (z : Packets W Y) (U : Config G n) (k : ℕ)
    (hS : scopes W k = joined W Y z.1.1)
    (hZ : inventory W k = z.1.1.biUnion (inventory W)) :
    (occurrence W Y z U : ℂ) =
      (if (z.1.1 : Set ℕ).Pairwise (fun i j => Disjoint (scopes W i) (scopes W j)) ∧
        joined W Y z.1.1 ∩ flags W.p.threshold U = z.1.1.biUnion (inventory W)
       then ∏ i ∈ z.1.1, (W.activities.K i U : ℂ) else 0) *
        coat W k (flip k z.1.2) U := by
  rw [coat_eq,hS,hZ]
  let I := z.1.1
  let J := z.1.2
  by_cases h : permits W (joined W Y I) (I.biUnion (inventory W)) J U
  · have he := eligible W _ _ (inventory_subset W Y I) J U h
    by_cases hp : (I : Set ℕ).Pairwise (fun i j => Disjoint (scopes W i) (scopes W j))
    · have ha : admitted W Y z.1 U := ⟨hp,h⟩
      dsimp only [I,J] at hp he h
      simp only [occurrence,if_pos ha,Complex.ofReal_mul,Complex.ofReal_prod,
        if_pos (And.intro hp he),waiting,if_pos h]
    · have ha : ¬admitted W Y z.1 U := fun ha => hp ha.1
      have hd : ¬((I : Set ℕ).Pairwise (fun i j => Disjoint (scopes W i) (scopes W j)) ∧
          joined W Y I ∩ flags W.p.threshold U = I.biUnion (inventory W)) := fun hd => hp hd.1
      dsimp only [I,J] at hd
      simp only [occurrence,if_neg ha,Complex.ofReal_zero,if_neg hd,zero_mul]
  have ha : ¬admitted W Y z.1 U := fun ha => h ha.2
  dsimp only [I,J] at h
  simp only [occurrence,if_neg ha,Complex.ofReal_zero,waiting,if_neg h,mul_zero]

end YM.Integration.ActualWilsonJoinedCofactor
