import YM.Pert.Attach.Partition

/-!
# Exact flag merger with polynomial-valued weights

Same overlap components and exclusions as `YM.Pert.Attach`, including on unmarked
factor selections from changing a vacuum mask/log. Extend the scalar reindexing to
arbitrary signed and nilpotent products (and without using `NoZeroDivisors`: dead
terms needn't be classified). Thus old K themselves can carry mixed markers;
attach to the WHOLE gas. This is on the actual RG torus support and predicates,
at a single fixed input/output threshold. No integration here, no change
of coupling or kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG03.Gather
open Lattice Wilson RG Function MeasureTheory Finset Pert.Attach
open scoped Topology BigOperators Classical
variable {n : Side} {G : Gauge} {A : Activities G n} {X : Corrections G n} {P : BudgetPoint}
variable {M : Type*} [CommMonoidWithZero M]
variable (A X)
/-- Weight already incorporates all pre-change exclusions. Choose any partition from the
true gas at this configuration, multiplying by any finite set of indicated logarithmic
correction factors minus one. -/
def initial (U : Config G n) (P : BudgetPoint) (W : Old → M) (s : Finset Old) :=
  if A.admissible P U s.toLeft then ∏ i ∈ s, W i else 0
/-- Keep all earlier tests on the merged address. -/
def outKey (U : Config G n) (P : BudgetPoint) (W : Old → M) (i : ℕ) :=
  if (page A X i).eligible P.threshold U then ∏ l ∈ parts A X i,W l else 0

def outWord (U : Config G n) (P : BudgetPoint) (W : Old → M) (b : Finset ℕ) :=
  if (attach A X P.threshold A).admissible P U b then ∏ i ∈ b, outKey A X U P W i else 0

variable {A X} {U : Config G n} {W : Old → M}

lemma split {b : Finset Old}
    (hX : ∀ j, Healthy P.threshold (X.region j) U → W (.inr j) = 0)
    (hb : initial A U P W b ≠ 0) :
    ∃ s, (attach A X P.threshold A).admissible P U s ∧ flatten A X s=b := by
  -- The geometry-only surjectivity already proved for real products:
  -- call on weight ONE rather than the quiet coefficient (the quiet
  -- coefficient may vanish identically on some old gas addresses).
  let A' := { A with K := fun _ _ => 1 }
  let Y : Corrections G n := { X with value := fun i V => if Healthy P.threshold (X.region i) V then (0:ℝ) else 1 }
  apply split_flatten (A:=A') (X:=Y) (R:=A) (fun j hj=> if_pos hj)
  unfold initial at hb; split_ifs at hb with h; swap; · contradiction
  unfold start; rw [if_pos (show A'.admissible P U b.toLeft from h)]
  rw [show ∏ l ∈ b, weight A' Y U l = 1 from prod_eq_one fun l hl => ?_]; norm_num
  cases l with
  | inl i => rfl
  | inr i => exact if_neg (fun hi => hb (prod_eq_zero hl (hX i hi)))

/-- Disjoint output supports imply no duplicate letter; even if a correction
is sold on the empty support (price test can't see that, but the weight has to
vanish by flag detection; such a letter also cannot be part of a fused address). -/
lemma area_not_empty {i : ℕ} {l : Old} (hl : l∈parts A X i) : (X.area A l).Nonempty := by
  obtain ⟨j,hj⟩ := (decoding A X i).2.2.1
  have hc := (decoding A X i).2.1.2 _ (mem_toLeft.mp hj) _ hl
  -- last hop touches its support
  cases hc with
  | refl => exact (A.forced j).inventory_ne.mono (A.forced j).inventory_sup
  | tail _ ha => obtain ⟨-, -, x, -, hx⟩:= ha; exact ⟨x,hx⟩

lemma matchWord (hK : ∀ j, W (.inl j) ≠ 0 → (A.forced j).eligible P.threshold U)
    {s : Finset ℕ} (h : (attach A X P.threshold A).admissible P U s) :
    outWord A X U P W s = initial A U P W (flatten A X s) := by
  rw [initial, outWord, if_pos h, if_pos (show A.admissible P U (flatten A X s).toLeft from
    ⟨flatten_pairwise (Or.inr trivial) h.1,(bills_flatten _).trans h.2⟩)]
  unfold flatten; rw [prod_biUnion ?_]
  · refine prod_congr rfl fun i hi => ?_
    unfold outKey
    split
    · rfl
    next hn =>
      symm
      by_contra! hp
      refine hn ⟨valid_out h hi,fun j hj => (hK j ?_).2⟩
      exact fun hz => hp (prod_eq_zero (mem_toLeft.mp hj) hz)
  · intro i hi j hj hn
    apply disjoint_left.mpr; intro l hl he
    obtain ⟨x,hx⟩ := area_not_empty hl
    exact disjoint_left.mp (h.1 hi hj hn) (show x∈full A X (parts A X i) from mem_biUnion.mpr ⟨l,hl,hx⟩)
      (show x∈full A X (parts A X j) from mem_biUnion.mpr ⟨l,he,hx⟩)

section
variable {N : Type*} [CommSemiring N] [TopologicalSpace N]
/-- Only surviving product choices needed for the identity. Evaluation
series may be vector valued (commuting) and need not be absolutely convergent
for this reindexing lemma; give true summability below before interpreting them. -/
theorem reindexed
    {W : Old → N}
    (hK : ∀ j, W (.inl j) ≠ 0 → (A.forced j).eligible P.threshold U)
    (hX : ∀ j, Healthy P.threshold (X.region j) U → W (.inr j)=0)
    (p : N) :
    HasSum (outWord A X U P W) p ↔ HasSum (initial A U P W) p := by
  let v := outWord A X U P W
  let w := initial A U P W
  have hs (s : Function.support v) : (attach A X P.threshold A).admissible P U s.val := by
    by_contra hn; exact s.property (if_neg hn)
  have he (s : Function.support v) : w (flatten A X s.val) = v s.val := (matchWord hK (hs s)).symm
  let f : Function.support v → Function.support w := fun i=>⟨flatten A X i.val,
    show w _ ≠ 0 from by rw [he i]; exact i.property⟩
  have hI : Injective f := by
    intro s t H
    apply Subtype.ext; apply image_injective (parts_inj A X)
    rw [← parts_flatten (hs s),← parts_flatten (hs t), show flatten A X s.val=flatten A X t.val from congrArg Subtype.val H]
  have hS : Surjective f := by
    intro b
    obtain ⟨s,h,e⟩:= split (X:=X) hX b.property
    exact ⟨⟨s, show v s ≠ 0 from fun k=> b.property (by unfold v at k; rw [matchWord hK h,e] at k; exact k)⟩, Subtype.ext e⟩
  exact (Equiv.ofBijective f ⟨hI,hS⟩).hasSum_iff_of_support he
end
end YM.RG03.Gather
