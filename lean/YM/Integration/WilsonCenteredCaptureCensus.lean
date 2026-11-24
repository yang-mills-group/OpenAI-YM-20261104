import YM.Integration.WilsonCenteredCaptureReconstruction

/-! A bijective census and its signed all-field sum. The serial of a held
source on an old owner bundle is fixed before the field and complement. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCaptureCensus
open Finset Lattice RG Wilson Push.Local Planned.GuardedAtom
open WilsonCenteredOriginalCaptureOwner
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} (P : Rep G n) (K : Guard.Keeper P.p P.activities)
    (D : Support n) (I : Finset ℕ) (U : Config G n) (serial : Finset ℕ → ℕ)

def host (C : Finset ℕ) : ℕ :=
  if live : C.Nonempty then K.code (docket P D C live (serial C)) else 0

abbrev Enter := {F : Finset ℕ // P.activities.admissible P.p U F ∧ I ⊆ F ∧
  (taken P D I F).Nonempty}

structure Ticket (C E : Finset ℕ) : Prop where
  live : C.Nonempty
  kept : I ⊆ C
  hits : ∀ i ∈ C, i ∈ I ∨ ¬Disjoint D (P.activities.forced i).support
  split : (C : Set ℕ).Pairwise (fun i j => Disjoint (P.activities.forced i).support (P.activities.forced j).support)
  fresh : host P K D serial C ∉ E
  admit : P.activities.admissible P.p U (insert (host P K D serial C) E)

abbrev Leave := {q : Finset ℕ × Finset ℕ // Ticket P K D I U serial q.1 q.2}

theorem admit (F : Enter P D I U) :
    Ticket P K D I U serial (taken P D I F.val) (F.val \ taken P D I F.val) := by
  obtain ⟨F,old,keep,live⟩ := F
  have core := (booked P K D I F U old live (serial (taken P D I F))).2.2
  refine ⟨live,fun _ hi => mem_filter.mpr ⟨keep hi,Or.inl hi⟩,fun _ hi=>(mem_filter.mp hi).2,
    fun _ hi _ hj ne=>old.1 (mem_filter.mp hi).1 (mem_filter.mp hj).1 ne,?_,?_⟩
  · simpa only [host,dif_pos live] using core.2.1
  · simpa only [host,dif_pos live] using core.2.2

theorem undo (C E : Finset ℕ) (q : Ticket P K D I U serial C E) :
    Disjoint C E ∧ P.activities.admissible P.p U (C ∪ E) ∧
    taken P D I (C ∪ E) = C ∧ (C ∪ E) \ C = E := by
  have h := q.fresh
  have b := q.admit
  rw [host,dif_pos q.live] at h b
  exact WilsonCenteredCaptureReconstruction.recovered P K D I C E U (serial C) q.live q.kept
    q.hits q.split h b

def equivalence : Enter P D I U ≃ Leave P K D I U serial where
  toFun F := ⟨(taken P D I F.val,F.val \ taken P D I F.val),admit P K D I U serial F⟩
  invFun q := ⟨q.val.1 ∪ q.val.2,by
    obtain ⟨_,old,h,_⟩ := undo P K D I U serial q.val.1 q.val.2 q.property
    exact ⟨old,q.property.kept.trans Finset.subset_union_left,by rw [h];exact q.property.live⟩⟩
  left_inv F := Subtype.ext (by
    change taken P D I F.val ∪ (F.val \ taken P D I F.val) = F.val
    exact Finset.union_sdiff_of_subset (filter_subset ..))
  right_inv q := Subtype.ext (by
    obtain ⟨_,_,hC,hE⟩ := undo P K D I U serial q.val.1 q.val.2 q.property
    apply Prod.ext
    · exact hC
    · change (q.val.1 ∪ q.val.2) \ taken P D I (q.val.1 ∪ q.val.2) = q.val.2
      rwa [hC])

def value (f : ℂ) (g : ℕ → ℂ) (C : Finset ℕ) : ℂ :=
  if (P.activities.forced (host P K D serial C)).eligible P.p.threshold U then
    (f * ∏ i ∈ I, g i) * ∏ j ∈ C \ I, (P.activities.K j U : ℂ) else 0

/-- The whole sum still integrates the original complement. In particular
an already deposited mixed hard coefficient uses one old owner. -/
theorem total (f : ℂ) (g : ℕ → ℂ) :
    (∑' F : Enter P D I U, (f * ∏ i ∈ I, g i) * ∏ j ∈ F.val \ I, (P.activities.K j U : ℂ)) =
    ∑' q : Leave P K D I U serial, value P K D I U serial f g q.val.1 *
      ∏ j ∈ q.val.2, (P.activities.K j U : ℂ) := by
  let e := equivalence P K D I U serial
  rw [←e.symm.tsum_eq (fun F : Enter P D I U => (f * ∏ i ∈ I, g i) * ∏ j ∈ F.val \ I, (P.activities.K j U : ℂ))]
  apply tsum_congr
  intro q
  obtain ⟨⟨C,E⟩,hq⟩ := q
  have h := hq.fresh
  have b := hq.admit
  rw [host,dif_pos hq.live] at h b
  change _ = value P K D I U serial f g C * ∏ j ∈ E, (P.activities.K j U : ℂ)
  rw [value,host,dif_pos hq.live]
  exact (WilsonCenteredCaptureReconstruction.emitted P K D I C E U (serial C) hq.live
    hq.kept hq.hits hq.split h b g f).symm

end YM.Integration.WilsonCenteredCaptureCensus
