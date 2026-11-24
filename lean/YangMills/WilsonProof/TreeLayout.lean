import YangMills.WilsonProof.TreeConvoy
import YM.OPE.Nesting.Geometry

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills.Hierarchy Function Finset OPE OPE.Arboreal OPE.Nesting
open scoped Classical BigOperators

abbrev arity (t : FusionTree) (v : t.Vertex) := Fintype.card (t.Child v)
def orderedChild (t : FusionTree) (v : t.Vertex) (i : Fin (arity t v)) : t.Child v :=
  (Fintype.equivFin (t.Child v)).symm i

theorem ordered_child_mem (t : FusionTree) (v : t.Vertex) (i : Fin (arity t v)) :
    childNode t (orderedChild t v i).1 ∈ (rawTree t).kids (.inl v) :=
  (childEquiv t v (orderedChild t v i)).2

/-- A recursive fork enumerates exactly its actual flat child fibre. -/
inductive Layout (t : FusionTree) : Node t → Nesting.Tree → Type where
  | leaf (i : Fin t.leaves) : Layout t (.inr i) .bud
  | fork (v : t.Vertex) (f : Fin (arity t v) → Nesting.Tree)
      (child : ∀ i, Layout t (childNode t (orderedChild t v i).1) (f i)) :
      Layout t (.inl v) (.fork (arity t v) f)

private theorem depth_le_sum (t : FusionTree) (a : Node t) :
    (rawTree t).depth a ≤ ∑ j : Node t, (rawTree t).depth j :=
  single_le_sum (fun j _ => Nat.zero_le ((rawTree t).depth j)) (mem_univ a)

theorem layout_exists (t : FusionTree) (a : Node t) : ∃ T : Nesting.Tree, Nonempty (Layout t a T) := by
  let μ (a : Node t) := (∑ j : Node t, (rawTree t).depth j) - (rawTree t).depth a
  refine (measure μ).wf.induction (C := fun b : Node t => ∃ U : Nesting.Tree, Nonempty (Layout t b U)) a ?_
  intro a ih
  cases a with
  | inr i => exact ⟨.bud, ⟨.leaf i⟩⟩
  | inl v =>
    have smaller (i : Fin (arity t v)) : μ (childNode t (orderedChild t v i).1) < μ (.inl v) := by
      have up := (rawTree t).higher (ordered_child_mem t v i)
      have cap := depth_le_sum t (childNode t (orderedChild t v i).1)
      dsimp only [μ]; omega
    choose f hf using fun i : Fin (arity t v) => ih _ (smaller i)
    exact ⟨.fork _ f, ⟨.fork v f (fun i => (hf i).some)⟩⟩

def recursiveTree (t : FusionTree) : Nesting.Tree := (layout_exists t (.inl 0)).choose

def rootLayout (t : FusionTree) : Layout t (.inl 0) (recursiveTree t) :=
  (layout_exists t (.inl 0)).choose_spec.some

namespace Layout
variable {t : FusionTree} {a : Node t} {T : Nesting.Tree}

def place : {a : Node t} → {T : Nesting.Tree} → Layout t a T → T.Positions → Node t
  | _, _, .leaf i, _ => .inr i
  | _, _, .fork v _ _, .inl _ => .inl v
  | _, _, .fork _ _ child, .inr ⟨i,j⟩ => place (child i) j

def vertex : {a : Node t} → {T : Nesting.Tree} → Layout t a T → T.Inner → t.Vertex
  | _, _, .leaf _, j => nomatch j
  | _, _, .fork v _ _, .inl _ => v
  | _, _, .fork _ _ child, .inr ⟨i,j⟩ => vertex (child i) j

def leafLabel : {a : Node t} → {T : Nesting.Tree} → Layout t a T → T.Leaf → Fin t.leaves
  | _, _, .leaf i, _ => i
  | _, _, .fork _ _ child, ⟨i,j⟩ => leafLabel (child i) j

@[simp] theorem place_top (h : Layout t a T) : h.place T.topSeat = a := by cases h <;> rfl

theorem place_leaf (h : Layout t a T) (i : T.Leaf) : h.place (T.leafSeat i) = .inr (h.leafLabel i) := by
  induction h with
  | leaf i => rfl
  | fork v f child ih => obtain ⟨i, j⟩ := i; exact ih i j

theorem leaf_below (h : Layout t a T) (i : T.Leaf) : (rawTree t).Anc a (.inr (h.leafLabel i)) := by
  induction h with
  | leaf i => exact OPE.Arboreal.Anc.same _ _
  | fork v f child ih =>
    obtain ⟨i, j⟩ := i
    exact (OPE.Arboreal.Anc.child (ordered_child_mem t v i)).joins (ih i j)

private theorem unique_child {I : Type} [Fintype I] (s : OPE.Arboreal I) {v j k l : I}
    (hj : j ∈ s.kids v) (hk : k ∈ s.kids v) (jl : s.Anc j l) (kl : s.Anc k l) : j = k := by
  have one {j k : I} (hj : j ∈ s.kids v) (hk : k ∈ s.kids v) (anc : s.Anc j k) : j = k := by
    by_contra ne
    have back := anc.back (fun equal => ne equal.symm)
    have pos := s.higher hj
    rw [((s.related _ _).1 hk).2] at back
    exact (not_le_of_gt pos) back.depth
  rcases jl.compare kl with a|b
  · exact one hj hk a
  · exact (one hk hj b).symm

theorem leaf_labels_bijective (h : Layout t a T) :
    Bijective (fun i : T.Leaf => (⟨h.leafLabel i, h.leaf_below i⟩ :
      {j : Fin t.leaves // (rawTree t).Anc a (.inr j)})) := by
  induction h with
  | leaf i =>
    constructor
    · intro j k _; exact @Subsingleton.elim Unit inferInstance j k
    · rintro ⟨j, hj⟩
      have eq : Sum.inr j = (Sum.inr i : Node t) := by
        by_contra ne; exact zone_inr t i (hj.proper ne)
      obtain rfl := Sum.inr_injective eq; exact ⟨(), rfl⟩
  | fork v f child ih =>
    constructor
    · rintro ⟨i, j⟩ ⟨k, l⟩ eq
      have equalLeaf : (child i).leafLabel j = (child k).leafLabel l := congrArg Subtype.val eq
      have anc := (child i).leaf_below j
      rw [equalLeaf] at anc
      have same := unique_child (rawTree t) (ordered_child_mem t v i) (ordered_child_mem t v k) anc ((child k).leaf_below l)
      have index : i = k := (Fintype.equivFin (t.Child v)).symm.injective
        (Subtype.ext (childNode_injective t same))
      subst k
      exact congrArg (Sigma.mk i) ((ih i).1 (Subtype.ext equalLeaf))
    · rintro ⟨l, anc⟩
      obtain ⟨b, hkid, down⟩ := anc.first Sum.inr_ne_inl
      let j := (childEquiv t v).symm ⟨b, hkid⟩
      let i := (Fintype.equivFin (t.Child v)) j
      have eq : childNode t (orderedChild t v i).1 = b := by
        change childNode t ((Fintype.equivFin (t.Child v)).symm ((Fintype.equivFin _) j)).1 = b
        rw [Equiv.symm_apply_apply]; exact congrArg Subtype.val ((childEquiv t v).apply_symm_apply ⟨b,hkid⟩)
      have sub : (rawTree t).Anc (childNode t (orderedChild t v i).1) (.inr l) := eq.symm ▸ down
      obtain ⟨k, e⟩ := (ih i).2 ⟨l, sub⟩
      have label : (child i).leafLabel k = l := congrArg (fun n :
        {j : Fin t.leaves // (rawTree t).Anc (childNode t (orderedChild t v i).1) (.inr j)} => n.1) e
      exact ⟨⟨i,k⟩, Subtype.ext label⟩

/-- No descendant leaf is lost or duplicated by the finite enumeration. -/
def leafEquiv (h : Layout t a T) : T.Leaf ≃ {j : Fin t.leaves // (rawTree t).Anc a (.inr j)} :=
  Equiv.ofBijective _ h.leaf_labels_bijective

theorem tapered {r β M η : ℝ} {s : t.Vertex → ℝ} {x : Fin t.leaves → E4} {z : t.Vertex → E4}
    (ad : ImmediateCourt t r β M η s x z) (hβ : 0 ≤ β) (h : Layout t a T) (bound : ℝ)
    (upper : ∀ v, a = .inl v → s v ≤ bound) : T.Tapered bound β (s ∘ h.vertex) := by
  induction h generalizing bound with
  | leaf i => trivial
  | fork v f child ih =>
    refine ⟨ad.2.1 v, upper v rfl, ?_⟩
    intro i
    apply ih i (s v * β)
    intro w eq
    have e := ((rawTree t).related _ _).1 (ordered_child_mem t v i)
    have size := child_scale ad hβ _ e.1
    rw [e.2, eq] at size
    change s w ≤ β * s v at size
    exact size.trans_eq (mul_comm β (s v))

theorem immediate {r β M η : ℝ} {s : t.Vertex → ℝ} {x : Fin t.leaves → E4} {z : t.Vertex → E4}
    (ad : ImmediateCourt t r β M η s x z) (h : Layout t a T) :
    Nesting.Tree.Immediate M η T (s ∘ h.vertex) (rawPosition t x z ∘ h.place) := by
  induction h with
  | leaf i => trivial
  | fork v f child ih =>
    have at_child (i : Fin (arity t v)) : rawPosition t x z ((child i).place (f i).topSeat) =
        t.positions x z (orderedChild t v i) := by
      rw [(child i).place_top]; exact rawPosition_child t v _ x z
    refine ⟨?_, ?_, ih⟩
    · intro i
      change ‖rawPosition t x z ((child i).place (f i).topSeat) - z v‖ ≤ M * s v
      rw [at_child]; exact (ad.2.2.2 v).1 _
    · intro i j ne
      change η * s v ≤ ‖rawPosition t x z ((child i).place (f i).topSeat) - rawPosition t x z ((child j).place (f j).topSeat)‖
      rw [at_child, at_child]; exact (ad.2.2.2 v).2 _ _ ((Fintype.equivFin _).symm.injective.ne ne)
end Layout

/-- At the root, every public leaf lies below the chosen vertex. -/
def recursiveLeaves (t : FusionTree) : (recursiveTree t).Leaf ≃ Fin t.leaves :=
  (rootLayout t).leafEquiv.trans
    { toFun := Subtype.val
      invFun := fun i => ⟨i, (rawTree t).closure (.inr i)⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }

theorem recursive_leaf_position (t : FusionTree) (x : Fin t.leaves → E4) (z : t.Vertex → E4)
    (i : (recursiveTree t).Leaf) :
    rawPosition t x z ((rootLayout t).place ((recursiveTree t).leafSeat i)) = x (recursiveLeaves t i) := by
  rw [(rootLayout t).place_leaf]; rfl

/-- The recursive APIs receive the original flat leaf tuple, vertex scales and centers. -/
theorem relative (t : FusionTree) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ C β : ℝ, 0 ≤ C ∧ β ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (r : ℝ) (s : t.Vertex → ℝ) (x : Fin t.leaves → E4) (z : t.Vertex → E4),
        ImmediateCourt t r β M η s x z →
        Nesting.Tree.Relative C (η/2) (recursiveTree t) (s ∘ (rootLayout t).vertex)
          (rawPosition t x z ∘ (rootLayout t).place) := by
  obtain ⟨C, β, hC, hb, conv⟩ := (recursiveTree t).of_immediate M η hM hη
  let B := min β (1/2)
  have hB : B ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_min hb.1 (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  refine ⟨C, B, hC, hB, ?_⟩
  intro r s x z ad
  have taper := (rootLayout t).tapered ad hB.1.le r (fun v e => by obtain rfl := Sum.inl_injective e; exact ad.1.le)
  exact conv _ _ r (taper.mono (min_le_left _ _) le_rfl) ((rootLayout t).immediate ad)

/-- Both original tree geometries accept every array below one strict cap. -/
theorem simultaneous (t : FusionTree) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ C β : ℝ, 0 ≤ C ∧ β ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (r : ℝ) (s : t.Vertex → ℝ) (x : Fin t.leaves → E4) (z : t.Vertex → E4),
        ImmediateCourt t r β M η s x z →
        (rawTree t).Convoy M (η/2) (rawScale t s) (rawPosition t x z) ∧
        Nesting.Tree.Relative C (η/2) (recursiveTree t) (s ∘ (rootLayout t).vertex)
          (rawPosition t x z ∘ (rootLayout t).place) := by
  obtain ⟨C,b,hC,hb,recursive⟩ := relative t hM hη
  have hc := ratioCap_mem t hM hη
  let β := min b (ratioCap t M η)
  refine ⟨C,β,hC,⟨lt_min hb.1 hc.1,(min_le_left _ _).trans_lt hb.2⟩,?_⟩
  intro r s x z ad
  have widen (u : ℝ) (hu : β ≤ u) : ImmediateCourt t r u M η s x z :=
    ⟨ad.1,ad.2.1,fun i => (ad.2.2.1 i).trans hu,ad.2.2.2⟩
  exact ⟨convoy hM hη (widen _ (min_le_right _ _)),recursive r s x z (widen _ (min_le_left _ _))⟩

end YM.Integration.WilsonSharpPhysicalTreeGeometry

