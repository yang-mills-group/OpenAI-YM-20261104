import YM.Integration.RunPhysicalMarks
import YM.Planned.ATOM_GUARDED_LAYOUT.Guards

/-! Pool all old supports meeting a source query, including an owner with
its flag outside that query. The joined address is available on the
original selected Wilson representation at the same capture date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredOriginalCaptureOwner
open Finset Lattice RG Wilson Push.Local PhysicalNext.Repeat.Legato Planned.GuardedAtom
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} (P : Rep G n)

def taken (D : Support n) (I F : Finset ℕ) : Finset ℕ :=
  F.filter (fun i => i ∈ I ∨ ¬Disjoint D (P.activities.forced i).support)

def ground (D : Support n) (C : Finset ℕ) : Support n :=
  D ∪ C.biUnion (fun i => (P.activities.forced i).support)

def flagsOf (C : Finset ℕ) : Support n :=
  C.biUnion (fun i => (P.activities.forced i).inventory)

theorem remaining (D : Support n) (I F : Finset ℕ) (U : Config G n)
    (old : P.activities.admissible P.p U F)
    (j : ℕ) (hj : j ∈ F \ taken P D I F) :
    Disjoint (ground P D (taken P D I F)) (P.activities.forced j).support := by
  rw [mem_sdiff] at hj
  have skip : ¬ (j ∈ I ∨ ¬Disjoint D (P.activities.forced j).support) := by
    intro sel
    exact hj.2 (mem_filter.mpr ⟨hj.1,sel⟩)
  have away : Disjoint D (P.activities.forced j).support := by tauto
  rw [Finset.disjoint_left]
  intro u hu hju
  rcases mem_union.mp hu with here | moved
  · exact Finset.disjoint_left.mp away here hju
  obtain ⟨i,hi,hui⟩ := mem_biUnion.mp moved
  have neq : i ≠ j := fun eq => hj.2 (eq ▸ hi)
  exact Finset.disjoint_left.mp (old.1 (mem_filter.mp hi).1 hj.1 neq) hui hju

theorem exact_flags (D : Support n) (I F : Finset ℕ) (U : Config G n)
    (old : P.activities.admissible P.p U F) :
    ground P D (taken P D I F) ∩ flags P.p.threshold U = flagsOf P (taken P D I F) := by
  ext y
  constructor
  · intro hi
    obtain ⟨query,bad⟩ := mem_inter.mp hi
    rw [←old.2] at bad
    obtain ⟨j,hj,hflag⟩ := mem_biUnion.mp bad
    by_cases hp : j ∈ taken P D I F
    · exact mem_biUnion.mpr ⟨j,hp,hflag⟩
    exact (Finset.disjoint_left.mp (remaining P D I F U old j (mem_sdiff.mpr ⟨hj,hp⟩))
      query ((P.activities.forced j).inventory_sup hflag)).elim
  · intro hi
    obtain ⟨j,hj,hflag⟩ := mem_biUnion.mp hi
    exact mem_inter.mpr ⟨mem_union_right D (mem_biUnion.mpr
      ⟨j,hj,(P.activities.forced j).inventory_sup hflag⟩),old.2 ▸
      mem_biUnion.mpr ⟨j,(mem_filter.mp hj).1,hflag⟩⟩

def docket (D : Support n) (C : Finset ℕ) (nonempty : C.Nonempty) (z : ℕ) : Dummy n :=
  (⟨(ground P D C,flagsOf P C),by
    obtain ⟨j,hj⟩ := nonempty
    obtain ⟨e,he⟩ := (P.activities.forced j).inventory_ne
    exact ⟨e,mem_biUnion.mpr ⟨j,hj,he⟩⟩,by
    intro x h
    obtain ⟨i,hi,he⟩ := mem_biUnion.mp h
    exact mem_union_right D (mem_biUnion.mpr ⟨i,hi,(P.activities.forced i).inventory_sup he⟩)⟩,z)

theorem booked (K : Guard.Keeper P.p P.activities) (D : Support n) (I F : Finset ℕ)
    (U : Config G n) (old : P.activities.admissible P.p U F)
    (nonempty : (taken P D I F).Nonempty) (z : ℕ) :
    let C := taken P D I F
    let E := F \ C
    let h := K.code (docket P D C nonempty z)
    (P.activities.forced h).support = ground P D C ∧
    (P.activities.forced h).inventory = flagsOf P C ∧
    (P.activities.forced h).eligible P.p.threshold U ∧ h ∉ E ∧
    P.activities.admissible P.p U (insert h E) := by
  intro C E h
  have support := K.support (docket P D C nonempty z)
  have inv := K.inventory (docket P D C nonempty z)
  change (P.activities.forced h).support = ground P D C at support
  change (P.activities.forced h).inventory = flagsOf P C at inv
  have exactFlag : (P.activities.forced h).support ∩ flags P.p.threshold U =
      (P.activities.forced h).inventory := by rw [support,inv];exact exact_flags P D I F U old
  have sep (j : ℕ) (hj : j ∈ E) : Disjoint (P.activities.forced h).support (P.activities.forced j).support := by
    rw [support]
    exact remaining P D I F U old j hj
  have fresh : h ∉ E := by
    intro he
    obtain ⟨y,hy⟩ := (P.activities.forced h).inventory_ne
    have hs := (P.activities.forced h).inventory_sup hy
    exact Finset.disjoint_left.mp (sep h he) hs hs
  refine ⟨support,inv,⟨exactFlag,K.pass (docket P D C nonempty z) U exactFlag⟩,fresh,?_,?_⟩
  · intro i hi j hj different
    rcases mem_insert.mp hi with rfl|hin
    · rcases mem_insert.mp hj with eq|hjn
      · exact (different eq.symm).elim
      · exact sep j hjn
    rcases mem_insert.mp hj with rfl|hjn
    · exact (sep i hin).symm
    · exact old.1 (mem_sdiff.mp hin).1 (mem_sdiff.mp hjn).1 different
  · rw [Finset.biUnion_insert,inv,←old.2]
    ext y
    constructor
    · intro hy
      rcases mem_union.mp hy with used|rest
      · obtain ⟨i,hi,hf⟩ := mem_biUnion.mp used
        exact mem_biUnion.mpr ⟨i,(mem_filter.mp hi).1,hf⟩
      · obtain ⟨i,hi,hf⟩ := mem_biUnion.mp rest
        exact mem_biUnion.mpr ⟨i,(mem_sdiff.mp hi).1,hf⟩
    · intro hy
      obtain ⟨i,hi,hf⟩ := mem_biUnion.mp hy
      by_cases hc : i ∈ C
      · exact mem_union_left _ (mem_biUnion.mpr ⟨i,hc,hf⟩)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_sdiff.mpr ⟨hi,hc⟩,hf⟩)

theorem original (R : Run G) (N p b : ℕ) (hb : b ≤ N) :
    let V := R.family.path.rep N p b
    ∃ K : Guard.Keeper V.p V.activities, (∀ k, V.activities.K (K.code k)=0) ∧
      ∀ D I F U, V.activities.admissible V.p U F → ∀ (live : (taken V D I F).Nonempty) (z : ℕ),
        let h := K.code (docket V D (taken V D I F) live z)
        (V.activities.forced h).eligible V.p.threshold U ∧ h ∉ F \ taken V D I F ∧
        V.activities.admissible V.p U (insert h (F \ taken V D I F)) := by
  intro V
  let slots := RunPhysicalMarks.actual_hasSlots R N p b hb
  refine ⟨Guard.Keeper.sufficient slots,Guard.Keeper.blank slots,?_⟩
  intro D I F U old live z
  exact (booked V (Guard.Keeper.sufficient slots) D I F U old live z).2.2

end YM.Integration.WilsonCenteredOriginalCaptureOwner
