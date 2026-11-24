import YangMills.WilsonProof.TreeNodes
import YM.OPE.Trees.Regime

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills.Hierarchy Function Finset OPE OPE.Arboreal
open scoped Classical BigOperators

/-- Leaves have no scale. The zero extension is only read at internal vertices by the raw estimates. -/
def rawScale (t : FusionTree) (s : t.Vertex → ℝ) : Node t → ℝ := Sum.elim s (fun _ => 0)

def rawPosition (t : FusionTree) (x : Fin t.leaves → E4) (z : t.Vertex → E4) : Node t → E4 := Sum.elim z x

@[simp] theorem rawPosition_child (t : FusionTree) (v : t.Vertex) (u : t.Child v)
    (x : Fin t.leaves → E4) (z : t.Vertex → E4) :
    rawPosition t x z (childEquiv t v u).1 = t.positions x z u := by
  obtain ⟨a, ha⟩ := u; cases a <;> rfl

variable {t : FusionTree} {r β M η : ℝ} {s : t.Vertex → ℝ} {x : Fin t.leaves → E4} {z : t.Vertex → E4}

/-- Geometry on immediate children, including empty child fibres. -/
abbrev ImmediateCourt (t : FusionTree) (r β M η : ℝ) (s : t.Vertex → ℝ)
    (x : Fin t.leaves → E4) (z : t.Vertex → E4) : Prop :=
  s 0 = r ∧ (∀ v, 0 < s v) ∧ (∀ i, t.ratio s i ≤ β) ∧
    ∀ v, YangMills.Hierarchy.Within (s v) M η (t.positions (v := v) x z) (z v)

theorem child_scale (h : ImmediateCourt t r β M η s x z) (hb : 0 ≤ β)
    (a : Node t) (ha : a ≠ (rawTree t).root) :
    rawScale t s a ≤ β * rawScale t s ((rawTree t).parent a) := by
  cases a with
  | inr i => exact mul_nonneg hb (h.2.1 _).le
  | inl v =>
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr (fun e => ha (congrArg Sum.inl e))
    exact (div_le_iff₀ (h.2.1 _)).mp (h.2.2.1 i)

theorem graduated (h : ImmediateCourt t r β M η s x z) (hb : β ∈ Set.Icc (0 : ℝ) 1) :
    (rawTree t).Graduated (rawScale t s) := by
  constructor
  · rintro (v|i) hv
    · exact h.2.1 v
    · exact (zone_inr t i hv).elim
  · intro a ha
    by_cases eq : a = (rawTree t).root
    · rw [eq, (rawTree t).direct]
    have pos : 0 ≤ rawScale t s ((rawTree t).parent a) := by cases a <;> exact (h.2.1 _).le
    exact (child_scale h hb.1 a eq).trans ((mul_le_mul_of_nonneg_right hb.2 pos).trans_eq (one_mul _))

theorem travel (h : ImmediateCourt t r β M η s x z) (hM : 0 ≤ M) (a : Node t) :
    ‖rawPosition t x z a - rawPosition t x z ((rawTree t).parent a)‖ ≤
      M * rawScale t s ((rawTree t).parent a) := by
  cases a with
  | inr i => exact (h.2.2.2 (t.attachLeaf i)).1 ⟨.inl i, rfl⟩
  | inl v =>
    refine Fin.cases ?_ (fun i => ?_) v
    · change ‖z 0 - z (t.parent 0)‖ ≤ M * s (t.parent 0)
      rw [t.rootFixed, sub_self, norm_zero]; exact mul_nonneg hM (h.2.1 _).le
    · exact (h.2.2.2 (t.parent i.succ)).1 ⟨.inr i, rfl⟩

theorem siblings (h : ImmediateCourt t r β M η s x z) (v : t.Vertex)
    (a b : ↥((rawTree t).kids (.inl v))) (hne : a ≠ b) :
    η * s v ≤ ‖rawPosition t x z a.1 - rawPosition t x z b.1‖ := by
  let e := childEquiv t v
  let A := e.symm a
  let B := e.symm b
  have ha : rawPosition t x z a.1 = t.positions x z A := by
    rw [←rawPosition_child, show childEquiv t v A = a from e.apply_symm_apply a]
  have hb : rawPosition t x z b.1 = t.positions x z B := by
    rw [←rawPosition_child, show childEquiv t v B = b from e.apply_symm_apply b]
  rw [ha, hb]
  exact (h.2.2.2 v).2 A B (e.symm.injective.ne hne)

/-- A fixed depth bound makes the immediate-to-cross-branch conversion uniform over all arrays. -/
def extent (t : FusionTree) (M : ℝ) : ℝ := (∑ i : Node t, ((rawTree t).depth i : ℝ)) * M

theorem extent_nonneg (t : FusionTree) {M : ℝ} (hM : 0 ≤ M) : 0 ≤ extent t M :=
  mul_nonneg (sum_nonneg (fun _ _ => Nat.cast_nonneg _)) hM

def ratioCap (t : FusionTree) (M η : ℝ) : ℝ := min (1 / 2) (η / (4 * (extent t M + 1)))

theorem ratioCap_mem (t : FusionTree) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ratioCap t M η ∈ Set.Ioo (0 : ℝ) 1 := by
  have he := extent_nonneg t hM
  exact ⟨lt_min (by norm_num) (div_pos hη (by positivity)), (min_le_left _ _).trans_lt (by norm_num)⟩

theorem cap_cost (t : FusionTree) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    4 * (extent t M * ratioCap t M η) ≤ η := by
  have he := extent_nonneg t hM
  have hb := (ratioCap_mem t hM hη).1
  have bounded := (le_div_iff₀ (show 0 < 4 * (extent t M + 1) by positivity)).mp
    (show ratioCap t M η ≤ η / (4 * (extent t M + 1)) from min_le_right _ _)
  linarith only [bounded, hb]

/-- Every raw fork separates all positions in distinct child subtrees. The bound includes internal centers. -/
theorem convoy (hM : 0 ≤ M) (hη : 0 < η) (h : ImmediateCourt t r (ratioCap t M η) M η s x z) :
    (rawTree t).Convoy M (η / 2) (rawScale t s) (rawPosition t x z) := by
  let T := rawTree t
  let X := rawPosition t x z
  let R := rawScale t s
  let β := ratioCap t M η
  let C := extent t M
  have hb : β ∈ Set.Ioo (0 : ℝ) 1 := ratioCap_mem t hM hη
  have hc : 0 ≤ C := extent_nonneg t hM
  have gr : T.Graduated R := graduated h ⟨hb.1.le, hb.2.le⟩
  have tv : ∀ a, ‖X a - X (T.parent a)‖ ≤ M * R (T.parent a) := travel h hM
  have near : T.Convoy M 0 R X := ⟨gr, tv, fun _ _ _ _ => by rw [zero_mul]; exact norm_nonneg _⟩
  have local_bound (i a j : Node t) (ha : a ∈ T.kids i) (hj : T.Anc a j) :
      ‖X j - X a‖ ≤ C * (β * R i) := by
    obtain ⟨notroot, par⟩ := (T.related _ _).1 ha
    have scale : R a ≤ β * R i := par ▸ child_scale h hb.1.le a notroot
    by_cases hz : a ∈ T.zones
    · have depth : ((T.depth j : ℕ) : ℝ) ≤ ∑ k : Node t, ((T.depth k : ℕ) : ℝ) :=
        single_le_sum (fun k _ => Nat.cast_nonneg (T.depth k)) (mem_univ j)
      calc ‖X j - X a‖ ≤ (T.depth j : ℝ) * (M * R a) := near.near hM hj hz
        _ ≤ C * R a := by
          rw [←mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right depth hM) (gr.allowed _ hz).le
        _ ≤ _ := mul_le_mul_of_nonneg_left scale hc
    · have eq : j = a := by by_contra hne; exact hz (hj.proper hne)
      have hi : i ∈ T.zones := par ▸ T.inward a
      rw [eq, sub_self, norm_zero]
      exact mul_nonneg hc (mul_nonneg hb.1.le (gr.allowed i hi).le)
  refine ⟨gr, tv, ?_⟩
  intro i j k fork
  have active := fork.inner
  obtain ⟨a, ha, b, hb', hab, hj, hk⟩ := fork
  have aj := local_bound i a j ha hj
  have bk := local_bound i b k hb' hk
  have centers : η * R i ≤ ‖X a - X b‖ := by
    cases i with
    | inr l => exact (zone_inr t l active).elim
    | inl v => exact siblings h v ⟨a, ha⟩ ⟨b, hb'⟩ (fun eq => hab (congrArg Subtype.val eq))
  have four : ‖X a - X b‖ ≤ ‖X j - X a‖ + ‖X j - X k‖ + ‖X k - X b‖ := by
    rw [norm_sub_rev (X j) (X a)]
    exact (c_dist_point (X a) (X k) (X b)).trans
      (add_le_add (c_dist_point (X a) (X j) (X k)) le_rfl)
  have cost := mul_le_mul_of_nonneg_right (cap_cost t hM hη) (gr.allowed i active).le
  change 4 * (C * β) * R i ≤ η * R i at cost
  linarith only [centers, four, aj, bk, cost]

end YM.Integration.WilsonSharpPhysicalTreeGeometry
