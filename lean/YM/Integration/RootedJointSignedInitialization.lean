import YM.Integration.JointSignedInitialization
import YM.RG3.Annuncia.Magic
import YM.PhysicalJoin.MarkedCore

/-!
Retain every origin/preimage as a separate old marker until the full joint
birth has been formed.  Native `Replica` excludes multiple alternatives of
one logical slot and inherits all product/counterterm exclusions.  Its exact
weighted aggregation is applied to the full density, before signed grouping.
Test weights are arbitrary; there is no choice of a source per test query.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.JointSignedInitialization
open Function Finset MeasureTheory Lattice Wilson RG Marker
open MergeProof MergeProof.Accent Extra.Trajectories
open scoped BigOperators Classical Topology

namespace Rooted
open RG3.Annuncia

variable {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (u : W → V) (R : Census V) (γ : W → ℂ)

omit [Fintype V] in
private theorem send_sum {A : Type} (q : R.Mode) (s : Finset A) (f : A → ℂ) :
    Poly.send q (∑ i ∈ s, f i) = ∑ i ∈ s, Poly.send q (f i) := by
  apply Marker.Poly.ext
  intro j
  simp only [Poly.part_send, Poly.part_sum]
  split <;> simp_all

/-- Weighted sums over every original root alternative in the same fibre. -/
def aggregate {X : Type} (F : W → X → ℂ) : V → X → ℂ :=
  fun v U => ∑ w : W, if v = u w then γ w * F w U else 0

theorem mouth_mach (f : W → ℂ) :
    Replica.mouth u R γ (Mach (Replica u R) f) =
      Mach R (fun v => ∑ w : W, if v = u w then γ w * f w else 0) := by
  have hs (w : W) :
      Replica.mouth u R γ (Poly.send ((Replica u R).fire w) (f w)) =
        Poly.send (R.fire (u w)) (γ w * f w) := by
    rw [Replica.mouth_apply, Replica.puts, Replica.that]
    congr 1
    simp [Replica.sign, Census.fire]
  unfold Mach
  rw [map_sum]
  simp_rw [hs]
  symm
  simp_rw [send_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_eq_single_of_mem (u w) (Finset.mem_univ _), if_pos rfl]
  intro v _ hv
  rw [if_neg hv, Poly.send_zero]

/-- Native origin aggregation acts on the complete original-vacuum birth.
Every fibre is summed exactly once, before any signed product projection. -/
theorem mouth_birth {G : Gauge} {n : Side} (P : Rep G n)
    (F : W → Config G n → ℂ) :
    (fun U => Replica.mouth u R γ (Accent.birth (Replica u R) P F U)) =
      Accent.birth R P (aggregate u γ F) := by
  funext U
  unfold Accent.birth
  rw [Replica.csmul, Replica.passed _ _ _ _ (mute _ _), mouth_mach]
  rfl

omit [Fintype V] in
/-- Aggregate after the actual joint push, or before it: the two complete
polynomials are equal on the same history and at the same coupling. -/
theorem mouth_gust {G : Gauge} (H : History G) (N p : ℕ)
    (P : Config G (H.S.side N p) → Poly (Replica u R))
    (hP : Integrable P (prior G (H.S.side N p))) {m : ℕ} (hm : m ≤ N) :
    gust H N p N (fun U => Replica.mouth u R γ (P U)) m hm =
      fun U => Replica.mouth u R γ (gust H N p N P m hm U) := by
  induction hm using Nat.decreasingInduction with
  | self => simp only [gust_base]
  | of_succ i hi ih =>
      rw [gust_step H N p N _ hi, ih]
      funext U
      rw [gust_step H N p N _ hi]
      unfold StepData.push
      let L := (Replica.cable u R γ).restrictScalars ℝ
      have he := L.integral_comp_comm
        (StepData.push_slice (H.levels.transition_mass i p (H.β N p (i + 1)))
          U _ (gust_live H N p N P hP hi))
      simp_rw [L.map_smul] at he
      exact he

end Rooted

section Signed
open RG3.Annuncia
variable {I J W : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
    {G : Gauge}

/-- Delete a region together with every one of its origin/preimage markers. -/
def keepOrigins (u : W → Name I J) (a : Finset I)
    (P : Poly (Replica u original)) : Poly (Replica u original) :=
  Poly.inject fun q =>
    if q.val.image (region ∘ u) ⊆ a then P.part q else 0

/-- Native origin aggregation commutes with deleting the complete preimage
of other regions.  The same weights and original source polynomial remain. -/
theorem mouth_keepOrigins (u : W → Name I J) (γ : W → ℂ) (a : Finset I)
    (P : Poly (Replica u original)) :
    Replica.mouth u original γ (keepOrigins u a P) =
      keepOriginal a (Replica.mouth u original γ P) := by
  apply Marker.Poly.ext
  intro q
  rw [Replica.quota]
  change (∑ j : (Replica u original).Mode,
      if Replica.bill u original j = q then
        Replica.sign u original γ j *
          (if j.val.image (region ∘ u) ⊆ a then P.part j else 0)
      else 0) =
    if q.val.image region ⊆ a then (Replica.mouth u original γ P).part q else 0
  have hi (j : (Replica u original).Mode) :
      j.val.image (region ∘ u) = (Replica.bill u original j).val.image region := by
    simp only [Replica.bill, Finset.image_image, Function.comp_def]
  by_cases hq : q.val.image region ⊆ a
  · rw [if_pos hq, Replica.quota]
    apply Finset.sum_congr rfl
    intro j _
    by_cases he : Replica.bill u original j = q
    · rw [if_pos he, if_pos he, hi j, he, if_pos hq]
    · rw [if_neg he, if_neg he]
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro j _
    by_cases he : Replica.bill u original j = q
    · rw [if_pos he, hi j, he, if_neg hq, mul_zero]
    · rw [if_neg he]

/-- The complete origin-to-signed-product initialization respects deletion
before aggregation and grouping, retaining the same singleton presentation. -/
theorem project_mouth_keepOrigins [Nonempty J]
    (u : W → Name I J) (γ : W → ℂ) (a : Finset I)
    (P : Poly (Replica u original)) :
    project (Replica.mouth u original γ (keepOrigins u a P)) =
      keepGrouped a (project (Replica.mouth u original γ P)) := by
  rw [mouth_keepOrigins, project_keep]

/-- One literal old polynomial contains every copy, product factor,
physical counterterm and origin alternative.  First sum the weighted root
alternatives with native `mouth`, then group complete signed branches.
No separate conditional means are multiplied. -/
theorem rooted_signed_gust (H : History G) (N p : ℕ)
    (u : W → Name I J) (γ : W → ℂ)
    (f : W → Config G (H.S.side N p) → ℂ)
    (hP : Integrable
      (Accent.birth (Replica u original) (H.rep N p N) f)
      (prior G (H.S.side N p))) {m : ℕ} (hm : m ≤ N) :
    let A := Rooted.aggregate u γ f
    let F := fun i j => A (Sum.inl (i, j))
    let K := fun i => A (Sum.inr i)
    gust H N p N (Accent.birth grouped (H.rep N p N) (signed F K)) m hm =
      fun U => project (Replica.mouth u original γ
        (gust H N p N (Accent.birth (Replica u original) (H.rep N p N) f) m hm U)) := by
  intro A F K
  have hsplit : sources F K = A := by
    funext a
    cases a <;> rfl
  have hbirth := Rooted.mouth_birth u original γ (H.rep N p N) f
  change (fun U => Replica.mouth u original γ
    (Accent.birth (Replica u original) (H.rep N p N) f U)) =
      Accent.birth original (H.rep N p N) A at hbirth
  rw [← hsplit] at hbirth
  have hA : Integrable (Accent.birth original (H.rep N p N) (sources F K))
      (prior G (H.S.side N p)) := by
    rw [← hbirth]
    exact ((Replica.cable u original γ).restrictScalars ℝ).integrable_comp hP
  rw [signed_gust H N p F K hA hm, ← hbirth,
    Rooted.mouth_gust u original γ H N p _ hP hm]

/-- Application to the native actual physical source supplier.  `W`
retains all individual copy/origin/preimage names; `u` records only which
logical product slot or counterterm they contribute to.  The original
top birth is integrable by `Marked.topLive`, not by an extra hypothesis.
Independent test weights enter only through the explicit `γ`. -/
theorem actual_rooted_signed_gust (C : Family G) (hC : C.Makes) (N p : ℕ)
    (u : W → Name I J) (γ : W → ℂ) (d : W → ℕ)
    (v : (w : W) → C.label (d w))
    (o : (j : ℕ) → W → Site (C.side j p)) (z : W → Extra.Histories.Motion)
    {m : ℕ} (hm : m ≤ N) :
    let f := PhysicalJoin.Marked.sourceItem d v o z N
    let A := Rooted.aggregate u γ f
    let F := fun i j => A (Sum.inl (i, j))
    let K := fun i => A (Sum.inr i)
    gust C.path N p N (Accent.birth grouped (C.path.rep N p N) (signed F K)) m hm =
      fun U => project (Replica.mouth u original γ
        (PhysicalJoin.Marked.pushedJoint d v o z (Replica u original) N m hm U)) := by
  intro f A F K
  exact rooted_signed_gust C.path N p u γ f
    (PhysicalJoin.Marked.topLive d v o z hC (Replica u original) N) hm

end Signed
end YM.Integration.JointSignedInitialization
