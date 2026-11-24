import YangMills.PhysicalOPE.FusionTree
import YM.OPE.Trees.Height

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills.Hierarchy Function Finset
open scoped Classical BigOperators

abbrev Node (t : FusionTree) := t.Vertex ⊕ Fin t.leaves

def vertexDepth (t : FusionTree) (v : t.Vertex) : ℕ := Nat.find (t.reachesRoot v)

theorem parent_depth_lt (t : FusionTree) (v : t.Vertex) (hv : v ≠ 0) :
    vertexDepth t (t.parent v) < vertexDepth t v := by
  have hit := Nat.find_spec (t.reachesRoot v)
  change t.parent^[vertexDepth t v] v = 0 at hit
  cases e : vertexDepth t v with
  | zero => rw [e] at hit; exact (hv hit).elim
  | succ n =>
    rw [e, iterate_succ_apply] at hit
    exact Nat.lt_succ_of_le (Nat.find_min' (t.reachesRoot (t.parent v)) hit)

/-- Raw positions are the disjoint union of all labelled internal vertices and all labelled leaves. -/
def rawTree (t : FusionTree) : OPE.Arboreal (Node t) where
  root := .inl 0
  zones := Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩
  parent := Sum.elim (fun v => .inl (t.parent v)) (fun i => .inl (t.attachLeaf i))
  depth := Sum.elim (vertexDepth t) (fun i => vertexDepth t (t.attachLeaf i) + 1)
  direct := congrArg Sum.inl t.rootFixed
  inward i := by cases i <;> simp
  step i h := by
    cases i with
    | inl v => exact parent_depth_lt t v (fun e => h (congrArg Sum.inl e))
    | inr i => exact Nat.lt_succ_self _

@[simp] theorem zone_inl (t : FusionTree) (v : t.Vertex) : Sum.inl v ∈ (rawTree t).zones := by
  simp [rawTree]
@[simp] theorem zone_inr (t : FusionTree) (i : Fin t.leaves) : Sum.inr i ∉ (rawTree t).zones := by
  simp [rawTree]
@[simp] theorem leaf_inr (t : FusionTree) (i : Fin t.leaves) : Sum.inr i ∈ (rawTree t).leaves :=
  ((rawTree t).leaves_are _).2 (zone_inr t i)
@[simp] theorem leaf_inl (t : FusionTree) (v : t.Vertex) : Sum.inl v ∉ (rawTree t).leaves := by
  rw [(rawTree t).leaves_are]; simp

/-- The original flat indexing is preserved literally in all four finite equivalences. -/
def zoneEquiv (t : FusionTree) : t.Vertex ≃ ↥(rawTree t).zones :=
  Equiv.ofBijective (fun v => ⟨.inl v, zone_inl t v⟩) (by
    constructor
    · intro a b h; exact Sum.inl_injective (congrArg Subtype.val h)
    · rintro ⟨v, hv⟩; cases v with
      | inl v => exact ⟨v, rfl⟩
      | inr i => exact (zone_inr t i hv).elim)

def leafEquiv (t : FusionTree) : Fin t.leaves ≃ ↥(rawTree t).leaves :=
  Equiv.ofBijective (fun i => ⟨.inr i, leaf_inr t i⟩) (by
    constructor
    · intro a b h; exact Sum.inr_injective (congrArg Subtype.val h)
    · rintro ⟨v, hv⟩; cases v with
      | inl v => exact (leaf_inl t v hv).elim
      | inr i => exact ⟨i, rfl⟩)

theorem proper_mem (t : FusionTree) (p : Node t) :
    p ∈ (rawTree t).middle (rawTree t).zones ↔ p ≠ (rawTree t).root ∧ p ∈ (rawTree t).zones := by
  simp only [OPE.Arboreal.middle, Finset.mem_erase]

def properEquiv (t : FusionTree) : Fin t.branches ≃ ↥((rawTree t).middle (rawTree t).zones) :=
  Equiv.ofBijective (fun i => ⟨.inl i.succ, (proper_mem t _).mpr
    ⟨fun h => Fin.succ_ne_zero i (Sum.inl_injective h), zone_inl t _⟩⟩) (by
    constructor
    · intro a b h; exact Fin.succ_injective _ (Sum.inl_injective (congrArg Subtype.val h))
    · rintro ⟨v, hv⟩; obtain ⟨ne, hz⟩ := (proper_mem t _).mp hv
      cases v with
      | inr i => exact (zone_inr t i hz).elim
      | inl v =>
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr (fun h => ne (congrArg Sum.inl h))
        exact ⟨i, rfl⟩)

def childNode (t : FusionTree) : Fin t.leaves ⊕ Fin t.branches → Node t :=
  Sum.elim Sum.inr (fun i => Sum.inl i.succ)

theorem childNode_injective (t : FusionTree) : Injective (childNode t) := by
  rintro (a|a) (b|b) h <;> simp_all [childNode]

def childEquiv (t : FusionTree) (v : t.Vertex) : t.Child v ≃ ↥((rawTree t).kids (.inl v)) :=
  Equiv.ofBijective (fun u => ⟨childNode t u.1, by
    obtain ⟨p, hp⟩ := u
    cases p with
    | inl i => exact ((rawTree t).related _ _).2 ⟨Sum.inr_ne_inl, congrArg Sum.inl hp⟩
    | inr j => exact ((rawTree t).related _ _).2 ⟨fun h => Fin.succ_ne_zero j (Sum.inl_injective h), congrArg Sum.inl hp⟩⟩) (by
    constructor
    · intro a b h; exact Subtype.ext (childNode_injective t (congrArg Subtype.val h))
    · rintro ⟨p, hp⟩; obtain ⟨ne, e⟩ := ((rawTree t).related _ _).1 hp
      cases p with
      | inr i => exact ⟨⟨.inl i, Sum.inl_injective e⟩, rfl⟩
      | inl v' =>
        obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (fun h => ne (congrArg Sum.inl h))
        exact ⟨⟨.inr j, Sum.inl_injective e⟩, rfl⟩)

@[simp] theorem zoneEquiv_val (t : FusionTree) (v : t.Vertex) : (zoneEquiv t v).1 = .inl v := rfl
@[simp] theorem leafEquiv_val (t : FusionTree) (i : Fin t.leaves) : (leafEquiv t i).1 = .inr i := rfl
@[simp] theorem properEquiv_val (t : FusionTree) (i : Fin t.branches) : (properEquiv t i).1 = .inl i.succ := rfl
@[simp] theorem childEquiv_val (t : FusionTree) (v : t.Vertex) (u : t.Child v) : (childEquiv t v u).1 = childNode t u.1 := rfl

theorem parent_iterate (t : FusionTree) (v : t.Vertex) (n : ℕ) :
    (rawTree t).parent^[n] (.inl v) = .inl (t.parent^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ih]; rfl

/-- The raw descendant predicate counts exactly the public labelled leaves below a vertex. -/
theorem leaf_ancestor (t : FusionTree) (v : t.Vertex) (i : Fin t.leaves) :
    (rawTree t).Anc (.inl v) (.inr i) ↔ ∃ n : ℕ, t.parent^[n] (t.attachLeaf i) = v := by
  constructor
  · rintro ⟨n, e⟩; cases n with
    | zero => exact (Sum.inr_ne_inl e).elim
    | succ n =>
      change (rawTree t).parent^[n] (.inl (t.attachLeaf i)) = .inl v at e
      rw [parent_iterate] at e; exact ⟨n, Sum.inl_injective e⟩
  · rintro ⟨n, h⟩; refine ⟨n+1, ?_⟩
    change (rawTree t).parent^[n] (.inl (t.attachLeaf i)) = .inl v
    rw [parent_iterate, h]

end YM.Integration.WilsonSharpPhysicalTreeGeometry
