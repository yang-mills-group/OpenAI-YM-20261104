import YM.Integration.WilsonOriginalHomogeneousShapeTensor
import YM.Integration.WilsonOriginalSeparatedChart

/-! A single positive separation for all physical configurations in an actual
affine unit cube about a separated point, at every finite occupied arity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalUniformPoseBox
open Set Filter Metric
open scoped Topology Classical

theorem original {n d : ℕ} (e : (Fin d → ℝ) ≃L[ℝ] Points n) {x : Points n} (hx : x ∈ conf n) :
    ∃ (a : Points n) (L : (Fin d → ℝ) ≃L[ℝ] Points n) (η : ℝ), 0 < η ∧
      (∀ i : Fin d, ‖L (Pi.single i (1:ℝ))‖ ≤ 1) ∧
      (∀ z : Fin d → ℝ, (∀ i, z i ∈ Icc (0:ℝ) 1) → ∀ i k : Fin n, i ≠ k →
        η ≤ dist ((a+L z) i) ((a+L z) k)) ∧
      a + L (fun _ => (1/2:ℝ)) = x := by
  let P := {p : Fin n × Fin n // p.1 ≠ p.2}
  have near (p : P) : ∀ᶠ η : ℝ in 𝓝[>] 0, η < dist (x p.val.1) (x p.val.2) :=
    (gt_mem_nhds (dist_pos.mpr (fun eq => p.property (hx eq)))).filter_mono nhdsWithin_le_nhds
  have pos : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  obtain ⟨η,hη,spent⟩ := (pos.and (eventually_all.mpr near)).exists
  let U := ⋂ p : P, {v : Points n | η < dist (v p.val.1) (v p.val.2)}
  have op : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro p
    exact isOpen_lt continuous_const (by fun_prop)
  obtain ⟨a,L,cols,cube,center⟩ := WilsonOriginalSeparatedChart.original e op
    (show x ∈ U from mem_iInter.mpr spent)
  refine ⟨a,L,η,hη,cols,?_,center⟩
  exact fun z hz i k neq => (mem_iInter.mp (cube z hz) (⟨(i,k),neq⟩:P)).le

end YM.Integration.WilsonOriginalUniformPoseBox
