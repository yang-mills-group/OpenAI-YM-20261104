import YM.Integration.WilsonOriginalPublicRelativeGramNativeUniform

/-! Changing the unit of length leaves the finite gauge group, sites and raw
normalized Wilson/FP reading unchanged on all subfaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramOuterMesh
open Filter Set Function Lattice RG Source PhysicalNext.Repeat.Legato XSpace XSpace.Cirrus
open XSpace.Expense Maxwell.Wick
open WilsonOriginalPublicPivotReflected (board sampled)
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : ℕ}

def home (M : Mesh) (T : ℝ) (pos : 0 < T) : Mesh :=
  ⟨M.p, M.spacing/T, div_pos M.positive pos⟩

def move (T : ℝ) (pos : 0 < T) (X : Sample n) : Sample n :=
  ⟨home X.F T pos, X.layout, T⁻¹ • X.center⟩

theorem area (M : Mesh) {T : ℝ} (pos : 0 < T) :
    (home M T pos).spacing = M.spacing/T ∧
    (home M T pos).size = M.size/T ∧ (home M T pos).p = M.p := by
  refine ⟨rfl, ?_, rfl⟩
  change M.spacing/T * (M.p.side.val:ℝ) = (M.spacing*(M.p.side.val:ℝ))/T
  ring

theorem site (X : Sample n) {T : ℝ} (pos : 0 < T) (i : Fin n) (k : Axis) :
    (familiar (move T pos X) i) k = T⁻¹*(familiar X i k) := by
  change (X.F.spacing/T)*(X.layout i k:ℝ)-(T⁻¹*X.center k) =
    T⁻¹*(X.F.spacing*(X.layout i k:ℝ)-X.center k)
  ring

theorem booked (X : Sample n) {T : ℝ} (pos : 0 < T) :
    welcome (move T pos X) ↔ welcome X := by
  have hs: (home X.F T pos).size=X.F.size/T := (area X.F pos).2.1
  change ((fun _ : Axis => (home X.F T pos).size/8) ≤ T⁻¹ • X.center ∧
      T⁻¹ • X.center ≤ (fun _ : Axis => (home X.F T pos).size/4)) ↔
    ((fun _ : Axis => X.F.size/8) ≤ X.center ∧ X.center ≤ (fun _ : Axis => X.F.size/4))
  rw [hs]
  constructor
  · rintro ⟨lo,hi⟩
    constructor
    · intro k
      have h := lo k
      change X.F.size/T/8 ≤ T⁻¹*X.center k at h
      have := mul_le_mul_of_nonneg_left h pos.le
      field_simp at this ⊢
      nlinarith
    · intro k
      have h := hi k
      change T⁻¹*X.center k ≤ X.F.size/T/4 at h
      have := mul_le_mul_of_nonneg_left h pos.le
      field_simp at this ⊢
      nlinarith
  · rintro ⟨lo,hi⟩
    constructor
    · intro k
      change X.F.size/T/8 ≤ T⁻¹*X.center k
      rw [show X.F.size/T/8=T⁻¹*(X.F.size/8) by ring]
      exact mul_le_mul_of_nonneg_left (lo k) (inv_pos.mpr pos).le
    · intro k
      change T⁻¹*X.center k ≤ X.F.size/T/4
      rw [show X.F.size/T/4=T⁻¹*(X.F.size/4) by ring]
      exact mul_le_mul_of_nonneg_left (hi k) (inv_pos.mpr pos).le

theorem ordinary (R : Run G) (W : Initialize G) (d : Fin n → ℕ)
    (v : (i : Fin n) → (R.family.labels.level (d i)).Coeff) (X : Sample n)
    (T : ℝ) (pos : 0 < T) (S : Finset (Fin n)) :
    board R W d v (move T pos X) S = board R W d v X S := rfl

theorem quadrature {L : Type*} [Fintype L] (R : Run G) (W : Initialize G) (d : Fin n → ℕ)
    (v : (i : Fin n) → (R.family.labels.level (d i)).Coeff) (X : L → Sample n) (μ : L → ℂ)
    (T : ℝ) (pos : 0 < T) (S : Finset (Fin n)) (q : ℕ) (u : ℝ) :
    sampled R W d v (fun l => move T pos (X l)) μ S q u = sampled R W d v X μ S q u := rfl

/-- The far reporting mesh can be selected first at its actual inverse pivot. -/
theorem together (M : Mesh) {T : ℝ} (pos : 0 < T) :
    home (home M T⁻¹ (inv_pos.mpr pos)) T pos = M := by
  cases M with
  | mk p s h =>
    simp [home, (ne_of_gt pos)]

end YM.Integration.WilsonOriginalPublicRelativeGramOuterMesh
end
