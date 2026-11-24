import YM.Marker.Truncated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Exact envelope bookkeeping for disjoint analytic input kernels.

An input kernel can use several independent test slots. Its envelope is paid
once at its distinguished slot, not once at every slot in that kernel. The
resulting per-slot product equals the original product of kernel envelopes
only on unions of complete input blocks. The support condition below is
therefore explicit and is preserved by the marker algebra.

The identities allow zero envelopes. They neither divide by an envelope nor
assert that a particular actual or formal output has the required support.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalKernelBlocks
open Marker
open scoped BigOperators Classical

variable {I V : Type*} [DecidableEq I] [DecidableEq V]

/-- Each analytic input retains its complete set of independent test slots
and one of its actual distinguished slots. -/
structure Layout (I V : Type*) [DecidableEq I] [DecidableEq V] where
  slots : I → Finset V
  root : I → V
  root_mem i : root i ∈ slots i
  disjoint {i j} : i ≠ j → Disjoint (slots i) (slots j)

namespace Layout
variable (B : Layout I V)

def assemble (A : Finset I) : Finset V := A.biUnion B.slots

theorem root_mem_assemble (A : Finset I) (i : I) :
    B.root i ∈ B.assemble A ↔ i ∈ A := by
  constructor
  · intro h
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp h
    by_cases he : i = j
    · simpa only [he] using hj
    exact False.elim ((Finset.disjoint_left.mp (B.disjoint he)) (B.root_mem i) hij)
  · intro h
    exact Finset.mem_biUnion.mpr ⟨i, h, B.root_mem i⟩

theorem root_injective : Function.Injective B.root := by
  intro i j h
  by_contra he
  exact (Finset.disjoint_left.mp (B.disjoint he)) (B.root_mem i)
    (h.symm ▸ B.root_mem j)

@[simp] theorem assemble_empty : B.assemble ∅ = ∅ := by
  simp [assemble]

theorem assemble_union (A C : Finset I) :
    B.assemble (A ∪ C) = B.assemble A ∪ B.assemble C := by
  simp [assemble, Finset.union_biUnion]

/-- No slot other than the distinguished slot is charged again for the same
analytic kernel. This definition works also for a zero envelope. -/
def slotCost [Fintype I] (cost : I → ℝ) (v : V) : ℝ :=
  ∏ i, if v = B.root i then cost i else 1

theorem slotCost_nonnegative [Fintype I] {cost : I → ℝ}
    (h : ∀ i, 0 ≤ cost i) (v : V) : 0 ≤ B.slotCost cost v := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact h i
  · exact zero_le_one

theorem slotCost_positive [Fintype I] {cost : I → ℝ}
    (h : ∀ i, 0 < cost i) (v : V) : 0 < B.slotCost cost v := by
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact h i
  · exact zero_lt_one

/-- The original envelope for every chosen analytic input occurs exactly once,
regardless of the number of independent test slots in that input. -/
theorem envelope_assemble [Fintype I] (cost : I → ℝ) (A : Finset I) :
    (∏ v ∈ B.assemble A, B.slotCost cost v) = ∏ i ∈ A, cost i := by
  unfold slotCost
  rw [Finset.prod_comm]
  simp only [Finset.prod_ite_eq', B.root_mem_assemble]
  exact Fintype.prod_ite_mem A cost

def Admissible (s : Finset V) : Prop := ∃ A : Finset I, B.assemble A = s

theorem admissible_empty : B.Admissible ∅ := ⟨∅, B.assemble_empty⟩

theorem admissible_union {s t : Finset V}
    (hs : B.Admissible s) (ht : B.Admissible t) : B.Admissible (s ∪ t) := by
  obtain ⟨A, rfl⟩ := hs
  obtain ⟨C, rfl⟩ := ht
  exact ⟨A ∪ C, B.assemble_union A C⟩

/-- The marker polynomial contains complete input blocks. Partial blocks
cannot be silently assigned the envelope of a whole analytic input. -/
def Supported {R : Census V} (F : Poly R) : Prop :=
  ∀ q : R.Mode, ¬ B.Admissible q.val → F.part q = 0

theorem supported_zero {R : Census V} : B.Supported (0 : Poly R) := by
  intro q _
  rfl

theorem supported_one {R : Census V} : B.Supported (1 : Poly R) := by
  intro q hq
  have hn : q ≠ R.quiet := by
    intro he
    apply hq
    simpa only [he, Census.quiet] using B.admissible_empty
  simp only [Poly.one_part, if_neg hn]

theorem supported_add {R : Census V} {F G : Poly R}
    (hF : B.Supported F) (hG : B.Supported G) : B.Supported (F + G) := by
  intro q hq
  rw [Poly.part_plus, hF q hq, hG q hq, add_zero]

theorem supported_smul {R : Census V} {F : Poly R}
    (hF : B.Supported F) (a : ℂ) : B.Supported (a • F) := by
  intro q hq
  rw [Poly.part_smul, hF q hq, mul_zero]

theorem supported_mul {R : Census V} {F G : Poly R}
    (hF : B.Supported F) (hG : B.Supported G) : B.Supported (F * G) := by
  intro q hq
  rw [Poly.part_mul]
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro t _
  split_ifs with hm
  · by_cases hs : B.Admissible s.val
    · have ht : ¬ B.Admissible t.val := by
        intro ht
        exact hq (hm.2 ▸ B.admissible_union hs ht)
      rw [hG t ht, mul_zero]
    · rw [hF s hs, zero_mul]
  · rfl

theorem supported_pow {R : Census V} {F : Poly R}
    (hF : B.Supported F) (n : ℕ) : B.Supported (F ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using B.supported_one (R := R)
  | succ n ih => simpa only [pow_succ] using B.supported_mul ih hF

theorem supported_sum {R : Census V} {J : Type*} (A : Finset J)
    (F : J → Poly R) (h : ∀ j ∈ A, B.Supported (F j)) :
    B.Supported (∑ j ∈ A, F j) := by
  intro q hq
  rw [Poly.part_sum]
  exact Finset.sum_eq_zero (fun j hj => h j hj q hq)

theorem supported_pass [Fintype V] {R : Census V} {F : Poly R}
    (hF : B.Supported F) : B.Supported (Poly.pass F) := by
  unfold Poly.pass
  exact B.supported_sum _ _ (fun n _ => B.supported_smul (B.supported_pow hF n) _)

theorem mode_envelope [Fintype I] {R : Census V} (cost : I → ℝ)
    (q : R.Mode) (A : Finset I) (h : B.assemble A = q.val) :
    Poly.toll (B.slotCost cost) q = ∏ i ∈ A, cost i := by
  unfold Poly.toll
  rw [← h]
  exact B.envelope_assemble cost A

/-- The selected block set is determined by its actual slot union. -/
theorem assemble_injective : Function.Injective B.assemble := by
  intro A C h
  ext i
  rw [← B.root_mem_assemble A i, ← B.root_mem_assemble C i, h]

theorem disjoint_of_assemble_disjoint {A C : Finset I}
    (h : Disjoint (B.assemble A) (B.assemble C)) : Disjoint A C := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact (Finset.disjoint_left.mp h)
    ((B.root_mem_assemble A i).mpr hi) ((B.root_mem_assemble C i).mpr hj)

theorem supported_send {R : Census V} (q : R.Mode) (hq : B.Admissible q.val)
    (a : ℂ) : B.Supported (Poly.send q a) := by
  intro s hs
  have hn : s ≠ q := by
    intro h
    exact hs (h.symm ▸ hq)
  simp only [Poly.part_send, if_neg hn]

theorem supported_neg {R : Census V} {F : Poly R}
    (hF : B.Supported F) : B.Supported (-F) := by
  intro q hq
  rw [Poly.part_neg, hF q hq, neg_zero]

theorem supported_sub {R : Census V} {F G : Poly R}
    (hF : B.Supported F) (hG : B.Supported G) : B.Supported (F - G) := by
  rw [sub_eq_add_neg]
  exact B.supported_add hF (B.supported_neg hG)

theorem supported_smul_real {R : Census V} {F : Poly R}
    (hF : B.Supported F) (a : ℝ) : B.Supported (a • F) := by
  intro q hq
  change a • F.part q = 0
  rw [hF q hq, smul_zero]

theorem supported_tsum_of_summable {R : Census V} {J : Type*} (F : J → Poly R)
    (hs : Summable F) (hF : ∀ j, B.Supported (F j)) :
    B.Supported (∑' j, F j) := by
  intro q hq
  change (Poly.get q) (∑' j, F j) = 0
  rw [(Poly.get q).map_tsum hs]
  calc
    _ = ∑' _ : J, (0 : ℂ) := tsum_congr (fun j => hF j q hq)
    _ = 0 := tsum_zero

/-- Support is also preserved by Lean's totalized infinite sum. This lemma does
not establish convergence of a physical series. -/
theorem supported_tsum {R : Census V} {J : Type*} (F : J → Poly R)
    (hF : ∀ j, B.Supported (F j)) : B.Supported (∑' j, F j) := by
  by_cases hs : Summable F
  · exact B.supported_tsum_of_summable F hs hF
  · rw [tsum_eq_zero_of_not_summable hs]
    exact B.supported_zero

/-- The original block product, defined only using a complete-block representation.
Its value outside that support is one and is never used for supported coefficients. -/
def blockEnvelope (cost : I → ℝ) (s : Finset V) : ℝ :=
  if h : B.Admissible s then ∏ i ∈ h.choose, cost i else 1

theorem blockEnvelope_assemble (cost : I → ℝ) (A : Finset I) :
    B.blockEnvelope cost (B.assemble A) = ∏ i ∈ A, cost i := by
  have h : B.Admissible (B.assemble A) := ⟨A, rfl⟩
  rw [blockEnvelope, dif_pos h]
  rw [B.assemble_injective h.choose_spec]

theorem blockEnvelope_eq_slots [Fintype I] (cost : I → ℝ) {s : Finset V}
    (h : B.Admissible s) :
    B.blockEnvelope cost s = ∏ v ∈ s, B.slotCost cost v := by
  obtain ⟨A, rfl⟩ := h
  rw [B.blockEnvelope_assemble, B.envelope_assemble]

theorem blockEnvelope_positive {cost : I → ℝ} (hc : ∀ i, 0 < cost i)
    (s : Finset V) : 0 < B.blockEnvelope cost s := by
  unfold blockEnvelope
  split_ifs
  · exact Finset.prod_pos (fun i _ => hc i)
  · exact zero_lt_one

/-- Only the actual supported coefficients can use the block-to-slot identity. -/
theorem blockEnvelope_part [Fintype I] {R : Census V} (cost : I → ℝ)
    {F : Poly R} (hF : B.Supported F) (q : R.Mode) :
    (B.blockEnvelope cost q.val : ℂ) * F.part q =
      (Poly.toll (B.slotCost cost) q : ℂ) * F.part q := by
  by_cases hq : B.Admissible q.val
  · rw [B.blockEnvelope_eq_slots cost hq]
    rfl
  · rw [hF q hq, mul_zero, mul_zero]

theorem blockEnvelope_merges {R : Census V} (cost : I → ℝ)
    {q s t : R.Mode} (hs : B.Admissible s.val) (ht : B.Admissible t.val)
    (hm : Poly.merges s t q) :
    B.blockEnvelope cost q.val = B.blockEnvelope cost s.val *
      B.blockEnvelope cost t.val := by
  obtain ⟨A, hA⟩ := hs
  obtain ⟨C, hC⟩ := ht
  have hAC : Disjoint A C := B.disjoint_of_assemble_disjoint (by rw [hA, hC]; exact hm.1)
  have hq : B.assemble (A ∪ C) = q.val := by rw [B.assemble_union, hA, hC, hm.2]
  rw [← hq, ← hA, ← hC, B.blockEnvelope_assemble,
    B.blockEnvelope_assemble, B.blockEnvelope_assemble, Finset.prod_union hAC]

end Layout

/-- Arbitrary disjoint input blocks. Empty blocks are permitted and their original
costs are retained as an explicit scalar factor below. -/
structure Family (I V : Type*) [DecidableEq I] [DecidableEq V] where
  slots : I → Finset V
  disjoint {i j} : i ≠ j → Disjoint (slots i) (slots j)

namespace Family
variable (B : Family I V)

abbrev Active := {i : I // (B.slots i).Nonempty}

def activeLayout : Layout B.Active V where
  slots i := B.slots i.val
  root i := i.property.choose
  root_mem i := i.property.choose_spec
  disjoint h := B.disjoint (fun he => h (Subtype.ext he))

def activeSelection (A : Finset I) : Finset B.Active :=
  A.subtype (fun i => (B.slots i).Nonempty)

theorem active_assemble (A : Finset I) :
    B.activeLayout.assemble (B.activeSelection A) = A.biUnion B.slots := by
  ext v
  constructor
  · intro h
    obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp h
    exact Finset.mem_biUnion.mpr ⟨i.val, by simpa [activeSelection] using hi, hv⟩
  · intro h
    obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp h
    have hn : (B.slots i).Nonempty := ⟨v, hv⟩
    exact Finset.mem_biUnion.mpr ⟨⟨i, hn⟩, by simpa [activeSelection] using hi, hv⟩

/-- Empty blocks carry no marker slot. Their costs remain in this explicit scalar,
not in a vacuum action or a fictitious anchor. -/
def emptyFactor (cost : I → ℝ) (A : Finset I) : ℝ :=
  ∏ i ∈ A, if (B.slots i).Nonempty then 1 else cost i

/-- The exact original cost product, including empty blocks and zero costs. -/
theorem cost_factorization [Fintype I] (cost : I → ℝ) (A : Finset I) :
    (∏ i ∈ A, cost i) = B.emptyFactor cost A *
      ∏ v ∈ A.biUnion B.slots, B.activeLayout.slotCost (fun i => cost i.val) v := by
  rw [← B.active_assemble, B.activeLayout.envelope_assemble]
  change (∏ i ∈ A, cost i) = B.emptyFactor cost A *
    ∏ i ∈ A.subtype (fun i => (B.slots i).Nonempty), cost i.val
  rw [Finset.prod_subtype_eq_prod_filter, Finset.prod_filter]
  unfold emptyFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

end Family
end YM.Integration.LocalKernelBlocks
