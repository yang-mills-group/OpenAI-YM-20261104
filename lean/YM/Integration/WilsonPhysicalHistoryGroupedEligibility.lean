import YM.Integration.WilsonPhysicalHistoryGroupedHard

/-! The regrouped old table follows the original full gauge, flag and
inventory tests, also when only the mixed source is submitted. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryGroupedEligibility
open Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open WilsonPhysicalHistoryGroupedHard
open scoped BigOperators Classical

variable {V T : Type*} [DecidableEq V] {Z : Census V} {G : Gauge} {n : Side}
  (P : Rep G n) (o : V → Site n) (H : Hard T P.p P.activities.forced P.activities.K o Z)
  (w : V → ℝ) (pos : ∀ v, 0 < w v) (keep : Finset Z.Mode)

theorem slot (t : T) (i : ℕ) :
    Flow o (barcode P.activities i) (column P o H keep t i) P.p.threshold := by
  let L := H.locality t i
  refine ⟨⟨fun U V h e => congrArg (select keep) (L.reads U V h e),
    fun g U => congrArg (select keep) (L.gauge g U), ?_, ?_⟩, ?_⟩
  · intro s
    change Measurable (fun U => if s ∈ keep then (H.hard t i U).part s else 0)
    by_cases take : s ∈ keep
    · simpa only [if_pos take, Function.comp_def] using (Poly.part_cont s).measurable.comp L.borel
    · simp only [if_neg take]
      exact measurable_const
  · intro U s apart
    change (if s ∈ keep then (H.hard t i U).part s else 0) = 0
    by_cases take : s ∈ keep
    · rw [if_pos take]
      exact not_not.mp fun nonzero => apart (L.carry U s nonzero)
    · exact if_neg take
  · intro U used
    have original : H.hard t i U ≠ 0 := by
      intro h
      apply used
      ext s
      change (if s ∈ keep then (H.hard t i U).part s else 0) = 0
      rw [h, Poly.part_nil]
      simp
    exact ⟨(H.charged t i U original).1, (P.activities.forced i).inventory_ne,
      (P.activities.forced i).inventory_sup⟩

include pos in
theorem physical {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a) (paid : H.Paid w B a cost)
    (t : T) (box : Box n) :
    Flow o box (grouped P o H keep t box) P.p.threshold := by
  exact transitK (barcode P.activities) (r:=id) (slot P o H keep t)
    (fun U => (Towed.repair (stored P o H w pos keep expo paid t) pos U).2) box

include pos in
theorem coefficient {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a) (paid : H.Paid w B a cost)
    (t : T) (box : Box n) (U : Config G n) (s : Z.Mode) :
    (grouped P o H keep t box U).part s =
      if s ∈ keep then
        ∑' i : {i // barcode P.activities i=box}, (H.hard t i.val U).part s else 0 := by
  have sum := (Towed.repair (stored P o H w pos keep expo paid t) pos U).2
  rw [show (grouped P o H keep t box U).part s =
      ∑' i : {i // barcode P.activities i=box}, (column P o H keep t i.val U).part s from
    Poly.share (sum.comp_injective Subtype.val_injective) s]
  by_cases take : s ∈ keep
  · rw [if_pos take]
    exact tsum_congr fun _ => if_pos take
  · rw [if_neg take]
    calc
      _ = ∑' _ : {i // barcode P.activities i=box}, (0:ℂ) := tsum_congr fun _ => if_neg take
      _ = 0 := tsum_zero

include pos in
theorem mixed [Fintype V] {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a) (paid : H.Paid w B a cost)
    (t : T) (box : Box n) (U : Config G n) :
    rises (grouped P o H (Finset.univ.filter (fun s : Z.Mode => 2 ≤ s.val.card)) t box U) := by
  intro s nonzero
  by_contra h
  apply nonzero
  rw [coefficient P o H w pos _ expo paid t box U s]
  simp [h]

end YM.Integration.WilsonPhysicalHistoryGroupedEligibility
end
