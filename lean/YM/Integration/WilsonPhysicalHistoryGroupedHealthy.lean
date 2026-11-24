import YM.Integration.WilsonPhysicalHistoryGroupedLamps
import YM.Push.LOCAL_SPLITTING.Atoms

/-! A nonclear old regular row has its original healthy indicator. It
therefore enters the genuine lower regular carton on exactly its support. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryGroupedHealthy
open Lattice Wilson RG Ac Marker Push Push.Local GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open WilsonPhysicalHistoryGroupedLamps
open scoped BigOperators Classical

variable {V T I : Type*} [DecidableEq V] {Z : Census V} {G : Gauge} {n : Side}
  {p : BudgetPoint} {o : V → Site n} (L : Lamps T I G p o Z)
  (w : V → ℝ) (pos : ∀ v, 0 < w v) (entries : Set I)

theorem lamp (clean : ∀ i ∈ entries, ¬ L.clear i) (t : T) (i : I) :
    Burns o (L.ground i) (row L entries t i) p.threshold := by
  by_cases kept : i ∈ entries
  · let f := masked p.threshold (L.ground i) (L.nominal t i)
    have rendered : row L entries t i = fun U => Poly.send (L.mode i) (f U) := by
      funext U
      simp only [row, if_pos kept, Lamps.frame, Lamps.light, if_neg (clean i kept), f]
    rw [rendered]
    have reads := uses_mask p.threshold (L.legal t i).sites
    have gauge := invariant_mask (L.legal t i).symmetry p.threshold (L.ground i)
    have measurable := masked_measurable p.threshold (L.ground i) _ (L.legal t i).borel
    refine ⟨⟨fun U V same flags => congrArg (Poly.send (L.mode i)) (reads U V same flags),
      fun g U => congrArg (Poly.send (L.mode i)) (gauge g U), ?_, ?_⟩, ?_, ?_⟩
    · intro s
      by_cases same : s=L.mode i
      · simpa only [Poly.part_send, if_pos same] using measurable
      · simp only [Poly.part_send, if_neg same]
        exact measurable_const
    · intro U s escaped
      rw [Poly.part_send]
      apply if_neg
      intro same
      apply escaped
      rw [same]
      exact fun _ hv => L.roots i _ hv
    · intro U used
      by_contra bad
      exact used (by rw [show f U=0 from masked_ne _ _ _ _ bad, Poly.send_zero])
    · intro U
      exact (Poly.part_send ..).trans (if_neg (L.live i).symm)
  · have missing : row L entries t i = fun _ => 0 := funext fun _ => if_neg kept
    rw [missing]
    refine ⟨⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ => measurable_const,
      fun _ _ _ => Poly.part_nil _⟩, fun _ h => (h rfl).elim, fun _ => Poly.part_nil _⟩

include pos in
theorem fields [Countable I] {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a) (paid : L.Paid w B a cost)
    (clean : ∀ i ∈ entries, ¬ L.clear i) (t : T) (support : Support n) :
    Burns o support (grouped L entries t support) p.threshold := by
  exact transitE L.ground (r:=id) (lamp L entries clean t)
    (fun U => (Towed.repair (stored L w pos entries expo paid t) pos U).2) support

include pos in
theorem mixed [Fintype V] {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a) (paid : L.Paid w B a cost)
    (many : ∀ i ∈ entries, 2 ≤ (L.mode i).val.card) (t : T) (support : Support n) (U : Config G n) :
    rises (grouped L entries t support U) := by
  have sum := (Towed.repair (stored L w pos entries expo paid t) pos U).2
  intro s used
  by_contra short
  apply used
  rw [show (grouped L entries t support U).part s =
      ∑' i : {i // L.ground i=support}, (row L entries t i.val U).part s from
    Poly.share (sum.comp_injective Subtype.val_injective) s]
  calc
    _ = ∑' _ : {i // L.ground i=support}, (0:ℂ) := by
      apply tsum_congr
      intro i
      by_cases selected : i.val ∈ entries
      · have different : s≠L.mode i.val := fun h => short (h ▸ many i.val selected)
        simp only [row, if_pos selected, Lamps.frame, Poly.part_send, if_neg different]
      · simp only [row, if_neg selected, Poly.part_nil]
    _ = 0 := tsum_zero

end YM.Integration.WilsonPhysicalHistoryGroupedHealthy
end
