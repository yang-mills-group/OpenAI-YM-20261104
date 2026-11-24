import YM.Integration.ActualWilsonTouchingVacuum

/-! Exact decomposition of the original Wilson gas at one designated
support. The untouched partners and all original signs are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonPacketSplit
open Function Finset Lattice RG Wilson
open scoped BigOperators Classical
variable {G : Gauge} {n : Side}

abbrev scopes (W : Rep G n) (j : ℕ) := (W.activities.forced j).support
abbrev inventory (W : Rep G n) (j : ℕ) := (W.activities.forced j).inventory

def aligned (W : Rep G n) (Y : Support n) (z : Finset ℕ × Finset ℕ) : Prop :=
  (∀ i ∈ z.1, ¬Disjoint (scopes W i) Y) ∧ ∀ j ∈ z.2, Disjoint (scopes W j) Y

abbrev Packets (W : Rep G n) (Y : Support n) := {z : Finset ℕ × Finset ℕ // aligned W Y z}

def partition (W : Rep G n) (Y : Support n) : Finset ℕ ≃ Packets W Y where
  toFun s := ⟨(s.filter (fun i => ¬Disjoint (scopes W i) Y),
    s.filter (fun i => Disjoint (scopes W i) Y)),
    fun _ hi => (mem_filter.1 hi).2,fun _ hi => (mem_filter.1 hi).2⟩
  invFun z := z.1.1 ∪ z.1.2
  left_inv s := by
    ext i
    by_cases h : Disjoint (scopes W i) Y <;> simp [h]
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      simp only [mem_filter,mem_union]
      constructor
      · rintro ⟨h,hY⟩
        exact h.resolve_right (fun hi => hY (z.2.2 i hi))
      · intro hi
        exact ⟨Or.inl hi,z.2.1 i hi⟩
    · ext i
      simp only [mem_filter,mem_union]
      constructor
      · rintro ⟨h,hY⟩
        exact h.resolve_left (fun hi => z.2.1 i hi hY)
      · intro hi
        exact ⟨Or.inr hi,z.2.2 i hi⟩

def joined (W : Rep G n) (Y : Support n) (I : Finset ℕ) := Y ∪ I.biUnion (scopes W)

theorem separated (W : Rep G n) (Y : Support n) (z : Packets W Y) :
    Disjoint z.1.1 z.1.2 := Finset.disjoint_left.2 fun j hI hJ => z.2.1 j hI (z.2.2 j hJ)

theorem inventory_union (W : Rep G n) (I J : Finset ℕ) :
    (I ∪ J).biUnion (inventory W) = I.biUnion (inventory W) ∪ J.biUnion (inventory W) := by
  ext x
  simp only [mem_biUnion,mem_union]
  aesop

/-- The original exact coverage condition with the touching packet fused to
one signed slot. Its inventory is the union of the original inventories. -/
def admitted (W : Rep G n) (Y : Support n) (z : Finset ℕ × Finset ℕ) (U : Config G n) :=
  (z.1 : Set ℕ).Pairwise (fun i j => Disjoint (scopes W i) (scopes W j)) ∧
  (z.2 : Set ℕ).Pairwise (fun i j => Disjoint (scopes W i) (scopes W j)) ∧
  (∀ j ∈ z.2, Disjoint (joined W Y z.1) (scopes W j)) ∧
    z.1.biUnion (inventory W) ∪ z.2.biUnion (inventory W) = flags W.p.threshold U

theorem admitted_iff (W : Rep G n) (Y : Support n) (z : Packets W Y) (U : Config G n) :
    admitted W Y z.1 U ↔ W.activities.admissible W.p U (z.1.1 ∪ z.1.2) := by
  let I := z.1.1
  let J := z.1.2
  have hd := Finset.disjoint_left.1 (separated W Y z)
  constructor
  · rintro ⟨hI,hJ,hcross,hcover⟩
    refine ⟨?_,(inventory_union W I J).trans hcover⟩
    have cross (i j : ℕ) (hi : i∈I) (hj : j∈J) : Disjoint (scopes W i) (scopes W j) :=
      Finset.disjoint_left.2 fun x hx hy => Finset.disjoint_left.1 (hcross j hj)
        (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i,hi,hx⟩)) hy
    intro i hi j hj hij
    rcases mem_union.1 hi with hi|hi <;> rcases mem_union.1 hj with hj|hj
    · exact hI hi hj hij
    · exact cross i j hi hj
    · exact (cross j i hj hi).symm
    exact hJ hi hj hij
  rintro ⟨hp,hcover⟩
  refine ⟨fun _ hi _ hj hij => hp (mem_union_left J hi) (mem_union_left J hj) hij,
    fun _ hi _ hj hij => hp (mem_union_right I hi) (mem_union_right I hj) hij,?_,
    (inventory_union W I J).symm.trans hcover⟩
  intro j hj
  apply Finset.disjoint_left.2
  intro x hx hy
  rcases mem_union.1 hx with hY|hI
  · exact Finset.disjoint_left.1 (z.2.2 j hj) hy hY
  obtain ⟨i,hi,hx⟩ := mem_biUnion.1 hI
  have hne : i ≠ j := fun e => hd hi (e ▸ hj)
  exact Finset.disjoint_left.1 (hp (mem_union_left J hi) (mem_union_right I hj) hne) hx hy

/-- A genuinely failed mask on an admitted packet has at least one
touching forced address. -/
theorem nonempty (W : Rep G n) (Y : Support n) (z : Packets W Y) (U : Config G n)
    (h : admitted W Y z.1 U) (hY : ¬Healthy W.p.threshold Y U) : z.1.1.Nonempty := by
  obtain ⟨x,hx,hflag⟩ := Finset.not_disjoint_iff.1 hY
  rw [←h.2.2.2] at hflag
  rcases mem_union.1 hflag with hI|hJ
  · obtain ⟨i,hi,_⟩ := mem_biUnion.1 hI
    exact ⟨i,hi⟩
  obtain ⟨j,hj,hz⟩ := mem_biUnion.1 hJ
  exact ((Finset.disjoint_left.1 (z.2.2 j hj)) ((W.activities.forced j).inventory_sup hz) hx).elim

def occurrence (W : Rep G n) (Y : Support n) (z : Packets W Y) (U : Config G n) : ℝ :=
  if admitted W Y z.1 U then (∏ i ∈ z.1.1, W.activities.K i U) *
    (∏ j ∈ z.1.2, W.activities.K j U) else 0

theorem occurrence_eq (W : Rep G n) (Y : Support n) (z : Packets W Y) (U : Config G n) :
    occurrence W Y z U = W.activities.gasOccurrence W.p (z.1.1 ∪ z.1.2) U := by
  unfold occurrence Activities.gasOccurrence
  by_cases h : admitted W Y z.1 U
  · rw [if_pos h,if_pos ((admitted_iff W Y z U).1 h),Finset.prod_union (separated W Y z)]
  rw [if_neg h,if_neg (h ∘ (admitted_iff W Y z U).2)]

theorem gas (W : Rep G n) (Y : Support n) (U : Config G n) :
    W.activities.gas W.p U = ∑' z : Packets W Y, occurrence W Y z U := by
  rw [← (partition W Y).tsum_eq (fun z => occurrence W Y z U)]
  apply tsum_congr
  intro s
  rw [occurrence_eq]
  exact congrArg (fun I => W.activities.gasOccurrence W.p I U) ((partition W Y).left_inv s).symm

end YM.Integration.ActualWilsonPacketSplit
