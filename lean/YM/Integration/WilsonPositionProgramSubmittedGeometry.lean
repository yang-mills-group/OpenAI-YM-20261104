import YM.RegulatorIR.Centered.View
import YM.XSpace.Layout

/-! The actual submitted center and each separated insertion in the fine units of the finite Wilson program. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramSubmittedGeometry
open Set MeasureTheory Lattice RegulatorIR RegulatorIR.Motion RegulatorIR.Spatial XSpace
open scoped Classical Topology
variable (M : Mesh)

def center (c : Four ℝ) : Room := fun a => c a/M.spacing

/-- Both boundary faces of the filed closed center box are allowed. -/
theorem pin (c : Four ℝ) (hc : c ∈ M.Box) : (1/8 : ℝ)*(M.p.side.val:ℝ) ≤
    singular (M.p.side.val : ℝ) (center M c) := by
  let P := (M.p.side.val : ℝ)
  let x := center M c
  have pos : 0 < P := by dsimp [P]; exact_mod_cast M.p.side.property
  have lo : P/8 ≤ x 0 := by
    apply (le_div_iff₀ M.positive).2
    have h := hc.1 (0:Axis)
    change M.spacing*P/8 ≤ c 0 at h
    linarith
  have hi : x 0 ≤ P/4 := by
    apply (div_le_iff₀ M.positive).2
    have h := hc.2 (0:Axis)
    change c 0 ≤ M.spacing*P/4 at h
    linarith
  let z := nearest (P/2) x
  refine le_trans ?_ (norm_le_pi_norm (x-slide (P/2) z) (0:Axis))
  change (1/8:ℝ)*P ≤ ‖x 0-P/2*(z 0 : ℝ)‖
  rw [Real.norm_eq_abs,le_abs]
  rcases le_or_gt (z 0) 0 with low | high
  · left
    have h0 : (z 0:ℝ) ≤ 0 := by exact_mod_cast low
    nlinarith [mul_nonpos_of_nonneg_of_nonpos pos.le h0]
  · right
    have h1 : 1 ≤ (z 0:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ z 0 from high)
    nlinarith [mul_nonneg pos.le (sub_nonneg.mpr h1)]

theorem displacement {n : ℕ} (z : Fin n → Cover) (c : Four ℝ) (i : Fin n) :
    dist (center M c) (slide 1 (z i))=‖WithLp.ofLp ((M.rel z c) i)‖/M.spacing := by
  have v : center M c-slide 1 (z i)=(-M.spacing⁻¹) • WithLp.ofLp ((M.rel z c) i) := by
    funext a
    change c a/M.spacing-1*(z i a:ℝ)= -M.spacing⁻¹*(M.spacing*(z i a:ℝ)-c a)
    field_simp [M.positive.ne']; ring
  rw [dist_eq_norm,v,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos M.positive,div_eq_mul_inv,mul_comm]

/-- One bound serves all positions in the submitted compact set and is independent of the mesh. -/
theorem roster {n : ℕ} (K : Set (Points n)) (compact : IsCompact K) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ M : Mesh, ∀ z : Fin n → Cover, ∀ c : Four ℝ, M.rel z c ∈ K →
      ∀ i, dist (center M c) (slide 1 (z i)) ≤ H/M.spacing := by
  have bounded (i : Fin n) : BddAbove ((fun x : Points n => ‖WithLp.ofLp (x i)‖) '' K) :=
    (compact.image (by fun_prop)).bddAbove
  choose H hH using bounded
  refine ⟨∑ i : Fin n, max 0 (H i),Finset.sum_nonneg fun i _ => le_max_left ..,?_⟩
  intro M z c inside i
  rw [displacement]
  apply div_le_div_of_nonneg_right _ M.positive.le
  exact (hH i (Set.mem_image_of_mem _ inside)).trans ((le_max_right ..).trans
    (Finset.single_le_sum (f:=fun i => max 0 (H i)) (fun _ _ => le_max_left ..) (Finset.mem_univ i)))

end YM.Integration.WilsonPositionProgramSubmittedGeometry
end
