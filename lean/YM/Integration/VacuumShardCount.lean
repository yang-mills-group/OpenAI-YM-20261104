import YM.Comparison.RG02.Order.Polar
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset

/-!
# Vacuum shards and finite slot-pattern counts

The total marker is literally quiet on the original Census and has n distinct
coupling occurrences. Every retained Hot block is consequently purely coupling
and has positive degree. This is a consequence of the native shard membership,
not a deletion of zero-degree terms from the general generator.

All counts concern the original finite shard set. No cardinality of the
external Census, physical alphabet, or Gaussian alphabet enters the bounds.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.VacuumShardCount

open Finset Function
open YM.Marker YM.Multi YM.Comparison.RG02.Order
open scoped BigOperators Classical

section Shards

variable {V : Type*} [DecidableEq V] {R : Census V}

private lemma member_subset (T : R.Mode) (q : (parts R).Mode)
    (hq : q ∈ shards R T) (i : Hot R) (hi : i ∈ q.val) :
    i.sites ⊆ T.val := by
  have hu : unionOf q = T := (mem_filter.mp hq).2
  intro x hx
  have h : x ∈ (unionOf q).val := mem_biUnion.mpr ⟨i, hi, hx⟩
  simpa only [hu] using h

private lemma support_sum (T : R.Mode) (q : (parts R).Mode)
    (hq : q ∈ shards R T) :
    (∑ i ∈ q.val, i.sites.card) = T.val.card := by
  have hu : unionOf q = T := (mem_filter.mp hq).2
  calc
    (∑ i ∈ q.val, i.sites.card) = (unionOf q).val.card :=
      (Finset.card_biUnion (parts_wise q)).symm
    _ = T.val.card := congrArg (fun s : R.Mode => s.val.card) hu

private lemma vertices_le_support (T : R.Mode) (q : (parts R).Mode)
    (hq : q ∈ shards R T) : q.val.card ≤ T.val.card := by
  calc
    q.val.card = ∑ _i ∈ q.val, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ q.val, i.sites.card :=
      Finset.sum_le_sum (fun i _ => Finset.card_pos.mpr i.property)
    _ = T.val.card := support_sum T q hq

private lemma shard_card_bound (T : R.Mode) :
    (shards R T).card ≤ 2 ^ (2 ^ T.val.card) := by
  let encode : (parts R).Mode → Finset (Finset V) :=
    fun q => q.val.image Hot.sites
  have hs : Injective (Hot.sites : Hot R → Finset V) :=
    fun _ _ h => Hot.eq_of_sites h
  have he : Injective encode := by
    intro q u h
    apply Subtype.ext
    exact Finset.image_injective hs h
  have hsub : (shards R T).image encode ⊆ T.val.powerset.powerset := by
    intro blocks hb
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hb
    apply mem_powerset.mpr
    intro block hk
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
    exact mem_powerset.mpr (member_subset T q hq i hi)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ he, Finset.card_powerset,
    Finset.card_powerset] at hcard
  exact hcard

end Shards

section Vacuum

variable {V : Type} [Fintype V] [DecidableEq V]
variable {R : Census V} {r : ℕ}

abbrev degree (i : Hot (Board R r)) : ℕ := (Join.right i.val).val.card

private lemma total_card {n : ℕ} (hn : n ≤ r) :
    (Join.pair R.quiet (pick r n)).val.card = n := by
  change ((∅ : Finset V).disjSum (pick r n).val).card = n
  rw [Finset.card_disjSum, Finset.card_empty, Nat.zero_add, picked r hn]

/-- Quiet total marker forces every retained vertex's original mark to quiet. -/
theorem member_left_quiet {n : ℕ} (q : (parts (Board R r)).Mode)
    (hq : q ∈ shards (Board R r) (Join.pair R.quiet (pick r n)))
    (i : Hot (Board R r)) (hi : i ∈ q.val) :
    Join.left i.val = R.quiet := by
  apply Subtype.ext
  change i.sites.toLeft = ∅
  have h := Finset.toLeft_subset_toLeft
    (member_subset (Join.pair R.quiet (pick r n)) q hq i hi)
  change i.sites.toLeft ⊆
    (R.quiet.val.disjSum (pick r n).val).toLeft at h
  rw [Finset.toLeft_disjSum] at h
  exact Finset.subset_empty.mp h

private lemma support_degree {n : ℕ} (q : (parts (Board R r)).Mode)
    (hq : q ∈ shards (Board R r) (Join.pair R.quiet (pick r n)))
    (i : Hot (Board R r)) (hi : i ∈ q.val) :
    i.sites.card = degree i := by
  have he := Join.pair_reunite i.val
  rw [member_left_quiet (R := R) (r := r) q hq i hi] at he
  have hc := congrArg (fun s : (Board R r).Mode => s.val.card) he
  change (R.quiet.val.disjSum (Join.right i.val).val).card = i.sites.card at hc
  rw [Finset.card_disjSum] at hc
  change 0 + degree i = i.sites.card at hc
  simpa only [Nat.zero_add] using hc.symm

/-- No zero-degree Hot vertex occurs in this particular quiet-total shard. -/
theorem member_degree_pos {n : ℕ} (q : (parts (Board R r)).Mode)
    (hq : q ∈ shards (Board R r) (Join.pair R.quiet (pick r n)))
    (i : Hot (Board R r)) (hi : i ∈ q.val) :
    0 < degree i := by
  rw [← support_degree (R := R) (r := r) q hq i hi]
  exact Finset.card_pos.mpr i.property

/-- The native disjoint union spends every coupling occurrence exactly once. -/
theorem degree_sum {n : ℕ} (hn : n ≤ r) (q : (parts (Board R r)).Mode)
    (hq : q ∈ shards (Board R r) (Join.pair R.quiet (pick r n))) :
    (∑ i ∈ q.val, degree i) = n := by
  calc
    (∑ i ∈ q.val, degree i) = ∑ i ∈ q.val, i.sites.card :=
      Finset.sum_congr rfl (fun i hi => (support_degree (R := R) (r := r) q hq i hi).symm)
    _ = (unionOf q).val.card :=
      (Finset.card_biUnion (parts_wise q)).symm
    _ = (Join.pair R.quiet (pick r n)).val.card :=
      congrArg (fun s : (Board R r).Mode => s.val.card) (mem_filter.mp hq).2
    _ = n := total_card (R := R) (r := r) hn

theorem vertex_count_le {n : ℕ} (hn : n ≤ r) (q : (parts (Board R r)).Mode)
    (hq : q ∈ shards (Board R r) (Join.pair R.quiet (pick r n))) :
    q.val.card ≤ n := by
  calc
    q.val.card = ∑ _i ∈ q.val, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ q.val, i.sites.card :=
      Finset.sum_le_sum (fun i _ => Finset.card_pos.mpr i.property)
    _ = (unionOf q).val.card :=
      (Finset.card_biUnion (parts_wise q)).symm
    _ = (Join.pair R.quiet (pick r n)).val.card :=
      congrArg (fun s : (Board R r).Mode => s.val.card) (mem_filter.mp hq).2
    _ = n := total_card (R := R) (r := r) hn

-- Checking the native dependent shard types needs a larger local kernel budget.
set_option maxHeartbeats 800000 in
/-- The full ordered vacuum tensor has j+2 slots at a degree-j vertex. -/
theorem leg_count_le {n : ℕ} (hn : n ≤ r) (q : (parts (Board R r)).Mode)
    (hq : q ∈ shards (Board R r) (Join.pair R.quiet (pick r n))) :
    (∑ i ∈ q.val, (degree i + 2)) ≤ 3 * n := by
  have hv := vertex_count_le (R := R) (r := r) hn q hq
  have hc : (∑ _i ∈ q.val, (2 : ℕ)) = q.val.card * 2 := by simp
  rw [Finset.sum_add_distrib, degree_sum (R := R) (r := r) hn q hq, hc]
  calc
    n + q.val.card * 2 ≤ n + n * 2 :=
      Nat.add_le_add_left (Nat.mul_le_mul_right 2 hv) n
    _ = 3 * n := by ring

/-- A crude bound on every original shard, independent of the external Census. -/
theorem shard_count_le {n : ℕ} (hn : n ≤ r) :
    (shards (Board R r) (Join.pair R.quiet (pick r n))).card ≤
      2 ^ (2 ^ n) := by
  simpa only [total_card (R := R) (r := r) hn] using
    shard_card_bound (Join.pair R.quiet (pick r n))

/-- Only slot kinds are enumerated here; Gaussian and physical labels are not. -/
abbrev SlotPatterns (K : Type*) (q : (parts (Board R r)).Mode) :=
  ∀ i : q.val, Fin (degree i.val + 2) → K

theorem pattern_count_le {K : Type*} [Fintype K] (hK : Fintype.card K ≤ 3)
    {n : ℕ} (hn : n ≤ r) (q : (parts (Board R r)).Mode)
    (hq : q ∈ shards (Board R r) (Join.pair R.quiet (pick r n))) :
    Fintype.card (SlotPatterns K q) ≤ 3 ^ (3 * n) := by
  have hc : Fintype.card (SlotPatterns K q) =
      Fintype.card K ^ (∑ i ∈ q.val, (degree i + 2)) := by
    change Fintype.card (∀ i : q.val, Fin (degree i.val + 2) → K) = _
    rw [Fintype.card_pi]
    simp_rw [Fintype.card_pi_const]
    rw [Finset.prod_pow_eq_pow_sum]
    exact congrArg (fun t : ℕ => Fintype.card K ^ t)
      (Finset.sum_coe_sort q.val (fun i : Hot (Board R r) => degree i + 2))
  rw [hc]
  exact (Nat.pow_le_pow_left hK _).trans
    (Nat.pow_le_pow_right (by decide) (leg_count_le (R := R) (r := r) hn q hq))

/-- The complete shard and slot-kind sum, before any site alphabet is chosen. -/
theorem total_pattern_count_le {K : Type*} [Fintype K] (hK : Fintype.card K ≤ 3)
    {n : ℕ} (hn : n ≤ r) :
    (∑ q ∈ shards (Board R r) (Join.pair R.quiet (pick r n)),
      Fintype.card (SlotPatterns K q)) ≤
        2 ^ (2 ^ n) * 3 ^ (3 * n) := by
  calc
    (∑ q ∈ shards (Board R r) (Join.pair R.quiet (pick r n)),
        Fintype.card (SlotPatterns K q)) ≤
      ∑ _q ∈ shards (Board R r) (Join.pair R.quiet (pick r n)),
        3 ^ (3 * n) :=
      Finset.sum_le_sum (fun q hq => pattern_count_le (R := R) (r := r) hK hn q hq)
    _ = (shards (Board R r) (Join.pair R.quiet (pick r n))).card *
        3 ^ (3 * n) := by simp
    _ ≤ 2 ^ (2 ^ n) * 3 ^ (3 * n) :=
      Nat.mul_le_mul_right _ (shard_count_le (R := R) (r := r) hn)

end Vacuum

end YM.Integration.VacuumShardCount
end
