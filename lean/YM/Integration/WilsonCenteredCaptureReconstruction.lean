import YM.Integration.WilsonCenteredOriginalCaptureOwner

/-! Undo the one-source collection at the original eligible complement.
The two finite products include every old unmarked factor, even when
several hard marks were already carried by the same old owner. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCaptureReconstruction
open Finset Lattice RG Wilson Push.Local Planned.GuardedAtom
open WilsonCenteredOriginalCaptureOwner
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} (P : Rep G n)

theorem recovered (K : Guard.Keeper P.p P.activities) (D : Support n)
    (I C E : Finset ℕ) (U : Config G n) (z : ℕ) (live : C.Nonempty)
    (kept : I ⊆ C) (hits : ∀ i ∈ C, i ∈ I ∨ ¬Disjoint D (P.activities.forced i).support)
    (compatible : (C : Set ℕ).Pairwise (fun i j => Disjoint (P.activities.forced i).support (P.activities.forced j).support))
    (noRepeat : K.code (docket P D C live z) ∉ E)
    (new : P.activities.admissible P.p U (insert (K.code (docket P D C live z)) E)) :
    Disjoint C E ∧ P.activities.admissible P.p U (C ∪ E) ∧
    taken P D I (C ∪ E) = C ∧ (C ∪ E) \ C = E := by
  let h := K.code (docket P D C live z)
  have dom := K.support (docket P D C live z)
  have inv := K.inventory (docket P D C live z)
  change (P.activities.forced h).support = ground P D C at dom
  change (P.activities.forced h).inventory = flagsOf P C at inv
  have whole (j : ℕ) (hj : j ∈ E) : Disjoint (ground P D C) (P.activities.forced j).support := by
    rw [←dom]
    exact new.1 (mem_insert_self h E) (mem_insert_of_mem hj) (fun eq => noRepeat (by change h ∈ E;rw [eq]; exact hj))
  have meets (i : ℕ) (hi : i ∈ C) (j : ℕ) (hj : j ∈ E) :
      Disjoint (P.activities.forced i).support (P.activities.forced j).support :=
    (whole j hj).mono_left (fun _ hx => mem_union_right D (mem_biUnion.mpr ⟨i,hi,hx⟩))
  have sep : Disjoint C E := by
    rw [Finset.disjoint_left]
    intro i hc he
    obtain ⟨x,hx⟩ := (P.activities.forced i).inventory_ne
    have hi := (P.activities.forced i).inventory_sup hx
    exact Finset.disjoint_left.mp (meets i hc i he) hi hi
  refine ⟨sep,⟨?_,?_⟩,?_,?_⟩
  · intro i hi j hj ne
    rcases mem_union.mp hi with hc|he <;> rcases mem_union.mp hj with jc|je
    · exact compatible hc jc ne
    · exact meets i hc j je
    · exact (meets j jc i he).symm
    · exact new.1 (mem_insert_of_mem he) (mem_insert_of_mem je) ne
  · rw [Finset.union_biUnion,←new.2,Finset.biUnion_insert,inv]
    rfl
  · ext i
    constructor
    · intro sel
      obtain ⟨hi,r⟩ := mem_filter.mp sel
      rcases mem_union.mp hi with hc|he
      · exact hc
      rcases r with marked|touch
      · exact kept marked
      exact (touch ((whole i he).mono_left Finset.subset_union_left)).elim
    · intro hi
      exact mem_filter.mpr ⟨mem_union_left _ hi,hits i hi⟩
  · ext i
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hc|he,notC⟩
      · exact (notC hc).elim
      · exact he
    · exact fun he => ⟨Or.inr he,fun hc => Finset.disjoint_left.mp sep hc he⟩

theorem products (I C E : Finset ℕ) (kept : I ⊆ C) (closed : Disjoint C E)
    (U : Config G n) (h : ℕ → ℂ) (f : ℂ) :
    (f * ∏ i ∈ I, h i) * (∏ j ∈ C \ I, (P.activities.K j U : ℂ)) *
        ∏ j ∈ E, (P.activities.K j U : ℂ) =
    (f * ∏ i ∈ I, h i) * ∏ j ∈ (C ∪ E) \ I, (P.activities.K j U : ℂ) := by
  have total : (C ∪ E) \ I = (C \ I) ∪ E := by
    ext j
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hc|he,hout⟩
      · exact Or.inl ⟨hc,hout⟩
      · exact Or.inr he
    · rintro (⟨hc,hout⟩|he)
      · exact ⟨Or.inl hc,hout⟩
      · exact ⟨Or.inr he,fun hi => Finset.disjoint_left.mp closed (kept hi) he⟩
  rw [total,Finset.prod_union (closed.mono_left Finset.sdiff_subset),mul_assoc]

/-- On every hosted configuration the exact original complement multiplies
the joint marked payload with all old predicates and all quiet partners.
The eligibility test in the new payload is evaluated on the original field. -/
theorem emitted (K : Guard.Keeper P.p P.activities) (D : Support n)
    (I C E : Finset ℕ) (U : Config G n) (z : ℕ) (live : C.Nonempty)
    (kept : I ⊆ C) (hits : ∀ i ∈ C, i ∈ I ∨ ¬Disjoint D (P.activities.forced i).support)
    (compatible : (C : Set ℕ).Pairwise (fun i j => Disjoint (P.activities.forced i).support (P.activities.forced j).support))
    (noRepeat : K.code (docket P D C live z) ∉ E)
    (new : P.activities.admissible P.p U (insert (K.code (docket P D C live z)) E))
    (h : ℕ → ℂ) (f : ℂ) :
    let key := K.code (docket P D C live z)
    (if (P.activities.forced key).eligible P.p.threshold U then
      (f * ∏ i ∈ I, h i) * ∏ j ∈ C \ I, (P.activities.K j U : ℂ)
     else 0) * ∏ j ∈ E, (P.activities.K j U : ℂ) =
      (f * ∏ i ∈ I, h i) * ∏ j ∈ (C ∪ E) \ I, (P.activities.K j U : ℂ) := by
  intro key
  obtain ⟨sep,old,ht,_⟩ := recovered P K D I C E U z live kept hits compatible noRepeat new
  have mask := exact_flags P D I (C ∪ E) U old
  rw [ht] at mask
  have exactFlag : (P.activities.forced key).support ∩ flags P.p.threshold U = (P.activities.forced key).inventory := by
    rw [K.support (docket P D C live z),K.inventory (docket P D C live z)]
    exact mask
  rw [if_pos (show (P.activities.forced key).eligible P.p.threshold U from
    ⟨exactFlag,K.pass (docket P D C live z) U exactFlag⟩)]
  exact products P I C E kept sep U h f

end YM.Integration.WilsonCenteredCaptureReconstruction
