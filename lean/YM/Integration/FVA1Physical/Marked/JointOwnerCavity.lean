import YM.RG.ActivityBounds

/-! Fix the complete finite set of occupied marked addresses of one
physical occurrence. After a simultaneous local repair their signed
scalar partners are precisely the noncrossing part of the repaired gas.
There is only one scalar vacuum for the joint set. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Finset Lattice RG Wilson
open scoped Classical BigOperators
variable {G : Gauge} {n : Side}
variable (A : Activities G n) (p : BudgetPoint)

def ownerUnion (l : Finset ℕ) := l.biUnion fun i => (A.forced i).support

def ownerInventory (l : Finset ℕ) := l.biUnion fun i => (A.forced i).inventory

def offOwners (l t : Finset ℕ) : Prop :=
  ∀ j∈t, Disjoint (ownerUnion A l) (A.forced j).support

def jointCompanions (l t : Finset ℕ) (U : Config G n) : ℝ :=
  if Disjoint l t ∧ A.admissible p U (l∪t) then ∏ j∈t,A.K j U else 0

def jointCrossing (l : Finset ℕ) (V : Config G n) : ℝ :=
  ∑' t,if offOwners A l t then 0 else A.gasOccurrence p t V

private theorem inventory_subset (l : Finset ℕ) : ownerInventory A l ⊆ ownerUnion A l := by
  intro x hx
  obtain ⟨j,hj,own⟩ := mem_biUnion.mp hx
  exact mem_biUnion.mpr ⟨j,hj,(A.forced j).inventory_sup own⟩

private theorem repair_live (l t : Finset ℕ) (U V : Config G n)
    (apart : (l:Set ℕ).Pairwise (fun i j => Disjoint (A.forced i).support (A.forced j).support))
    (present : ownerInventory A l ⊆ flags p.threshold U)
    (vacated : flags p.threshold V=flags p.threshold U \ ownerInventory A l) :
    (Disjoint l t ∧ A.admissible p U (l∪t)) ↔ offOwners A l t ∧ A.admissible p V t := by
  constructor
  · rintro ⟨dis,active⟩
    have free : offOwners A l t := by
      intro j hj;apply disjoint_left.mpr;intro x inl xj
      obtain ⟨i,hi,xi⟩ := mem_biUnion.mp inl
      have ne : i≠j := fun e => disjoint_left.mp dis (e ▸ hi) hj
      exact disjoint_left.mp (active.1 (mem_union_left _ hi) (mem_union_right _ hj) ne) xi xj
    refine ⟨free,fun i hi j hj ne => active.1 (mem_union_right _ hi) (mem_union_right _ hj) ne,?_⟩
    rw [vacated];ext x
    constructor
    · intro h
      obtain ⟨j,hj,own⟩ := mem_biUnion.mp h
      refine mem_sdiff.mpr ⟨?_,fun xl => disjoint_left.mp (free j hj)
        (inventory_subset A l xl) ((A.forced j).inventory_sup own)⟩
      rw [←active.2];exact mem_biUnion.mpr ⟨j,mem_union_right _ hj,own⟩
    intro h
    obtain ⟨xf,notl⟩ := mem_sdiff.mp h
    rw [←active.2] at xf
    obtain ⟨j,hj,own⟩ := mem_biUnion.mp xf
    rcases mem_union.mp hj with hl|ht
    · exact (notl (mem_biUnion.mpr ⟨j,hl,own⟩)).elim
    exact mem_biUnion.mpr ⟨j,ht,own⟩
  rintro ⟨free,rest⟩
  have dis : Disjoint l t := by
    apply disjoint_left.mpr;intro j hl ht
    obtain ⟨x,hx⟩ := (A.forced j).inventory_ne
    have xs := (A.forced j).inventory_sup hx
    exact disjoint_left.mp (free j ht) (mem_biUnion.mpr ⟨j,hl,xs⟩) xs
  refine ⟨dis,?_,?_⟩
  · intro i hi j hj ne
    change i∈l∪t at hi;change j∈l∪t at hj
    rcases mem_union.mp hi with il|it <;> rcases mem_union.mp hj with jl|jt
    · exact apart il jl ne
    · exact (free j jt).mono_left (by intro x hx; exact mem_biUnion.mpr ⟨i,il,hx⟩)
    · exact ((free i it).mono_left (by intro x hx; exact mem_biUnion.mpr ⟨j,jl,hx⟩)).symm
    exact rest.1 it jt ne
  rw [union_biUnion,rest.2,vacated]
  exact union_sdiff_of_subset present

theorem joint_owner_exterior (l : Finset ℕ) (U V : Config G n) (reads : A.ForcedFamily p)
    (apart : (l:Set ℕ).Pairwise (fun i j => Disjoint (A.forced i).support (A.forced j).support))
    (present : ownerInventory A l ⊆ flags p.threshold U)
    (vacated : flags p.threshold V=flags p.threshold U \ ownerInventory A l)
    (outside : ∀ e : Edge (Site n),e.1 ∉ ownerUnion A l → U e=V e) (t : Finset ℕ) :
    jointCompanions A p l t U = if offOwners A l t then A.gasOccurrence p t V else 0 := by
  have eq := repair_live A p l t U V apart present vacated
  unfold jointCompanions
  by_cases off : offOwners A l t
  · rw [if_pos off,Activities.gasOccurrence]
    by_cases active : A.admissible p V t
    · rw [if_pos (eq.mpr ⟨off,active⟩),if_pos active]
      apply prod_congr rfl;intro k hk
      apply reads.reads k U V
      · intro e head _tail
        exact outside e (fun xl => disjoint_left.mp (off k hk) xl head)
      rw [vacated];ext x;simp only [mem_inter,mem_sdiff]
      exact ⟨fun h => ⟨h.1,h.2,fun own => disjoint_left.mp (off k hk) (inventory_subset A l own) h.1⟩,
        fun h => ⟨h.1,h.2.1⟩⟩
    rw [if_neg (fun both => active (eq.mp both).2),if_neg active]
  rw [if_neg (fun both => off (eq.mp both).1),if_neg off]

theorem joint_owner_total {δ w : ℝ} (valid : A.Valid p δ w) (l : Finset ℕ) (U V : Config G n)
    (apart : (l:Set ℕ).Pairwise (fun i j => Disjoint (A.forced i).support (A.forced j).support))
    (present : ownerInventory A l ⊆ flags p.threshold U)
    (vacated : flags p.threshold V=flags p.threshold U \ ownerInventory A l)
    (outside : ∀ e : Edge (Site n),e.1 ∉ ownerUnion A l → U e=V e) :
    (∑' t,jointCompanions A p l t U) = A.gas p V - jointCrossing A p l V := by
  let g := fun t => A.gasOccurrence p t V
  let X := fun t => if offOwners A l t then 0 else g t
  have total : Summable g := (Activities.gasSeries valid).summable V
  have cross : Summable X := by
    apply (total.indicator {t | ¬offOwners A l t}).congr
    intro t;by_cases good : offOwners A l t <;> simp [X,good]
  change _=(∑' t,g t)-∑' t,X t
  rw [←total.tsum_sub cross]
  apply tsum_congr;intro t
  rw [joint_owner_exterior A p l U V valid.forced apart present vacated outside t]
  by_cases good : offOwners A l t <;> simp [g,X,good]

end YM.Integration.FVA1Physical.Marked
