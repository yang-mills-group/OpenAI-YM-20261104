import YM.Integration.WilsonOriginalUniformPoseBox

/-! An actual finite cover of a separated compact by inner thirds of legal
test boxes. The outer box has the same pose, coordinates and positive gap. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompactPoseCover
open Set Filter Metric
open scoped Classical Topology

structure Box (n d : ℕ) where
  origin : Points n
  axes : (Fin d → ℝ) ≃L[ℝ] Points n
  gap : ℝ
  positive : 0 < gap
  columns : ∀ i : Fin d, ‖axes (Pi.single i (1:ℝ))‖ ≤ 1
  separated : ∀ z : Fin d → ℝ, (∀ i, z i ∈ Icc (0:ℝ) 1) → ∀ i k : Fin n, i ≠ k →
    gap ≤ dist ((origin+axes z) i) ((origin+axes z) k)

def Box.atPhysical {n d : ℕ} (B : Box n d) (x : Points n) : Fin d → ℝ :=
  B.axes.symm (x-B.origin)

def Box.core {n d : ℕ} (B : Box n d) := {x : Points n | ∀ i, B.atPhysical x i ∈ Ioo (1/3:ℝ) (2/3)}

theorem Box.places {n d : ℕ} (B : Box n d) (x : Points n) : B.origin+B.axes (B.atPhysical x) = x := by
  rw [Box.atPhysical,ContinuousLinearEquiv.apply_symm_apply]
  abel

theorem original {n d : ℕ} (e : (Fin d → ℝ) ≃L[ℝ] Points n) (K : Set (Points n))
    (compact : IsCompact K) (clear : K ⊆ conf n) :
    ∃ roster : Finset (Box n d), ∀ x ∈ K, ∃ B ∈ roster, x ∈ B.core := by
  have enter (y : K) : ∃ B : Box n d, y.val ∈ B.core := by
    obtain ⟨a,L,η,good,cols,wide,center⟩ := WilsonOriginalUniformPoseBox.original e (clear y.property)
    let B : Box n d := ⟨a,L,η,good,cols,wide⟩
    refine ⟨B,?_⟩
    have value : B.atPhysical y.val = fun _ => (1/2:ℝ) := by
      change L.symm (y.val-a) = _
      rw [←center,add_sub_cancel_left,ContinuousLinearEquiv.symm_apply_apply]
    intro i
    rw [value]
    norm_num
  choose chart mem using enter
  have op (y : K) : IsOpen (chart y).core := by
    change IsOpen {x : Points n | ∀ i, (chart y).atPhysical x i ∈ Ioo (1/3:ℝ) (2/3)}
    simp only [setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_Ioo.preimage ((continuous_apply i).comp ((chart y).axes.symm.continuous.comp
      (continuous_id.sub continuous_const)))
  obtain ⟨used,inc⟩ := compact.elim_finite_subcover (fun y => (chart y).core) op
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,mem ⟨x,hx⟩⟩)
  refine ⟨used.image chart,?_⟩
  intro x hx
  obtain ⟨y,hy⟩ := mem_iUnion.mp (inc hx)
  obtain ⟨hy,hx⟩ := mem_iUnion.mp hy
  exact ⟨chart y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,hx⟩

end YM.Integration.WilsonOriginalCompactPoseCover
