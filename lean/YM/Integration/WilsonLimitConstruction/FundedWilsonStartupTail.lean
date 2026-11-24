import YM.Integration.WilsonLimitConstruction.FundedWilsonStartup

/-! A single four-link norm pays the original, prescribed unspent UV term.
The constants and all derivative estimates are fixed before any lattice or
period. The inverse-square coupling consumes exactly two powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonStartupTail

open Filter Function Metric Lattice Wilson RG Exterior WilsonStartup
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

def links (G : Gauge) (x : Quad.Dir G) : Quad.Group G := fun i => G.lieExp (x i)
def row (G : Gauge) (r : ℕ) (x : Quad.Dir G) := unspent (r+2) (Quad.read (links G x))

theorem jet (G : Gauge) (r : ℕ) : ContDiff ℝ ω (row G r) ∧ FlatAt (r+3) (row G r) 0 := by
  have hm : ContDiff ℝ ω (Quad.mat ∘ links G) := contDiff_pi.mpr fun i =>
    G.exp_jet.comp (contDiff_apply ..)
  have he : row G r = Quad.strokes (G := G) (r+2) [] ∘ Quad.mat ∘ links G := by
    funext x
    simp [row,comp_apply,Quad.strokes,Quad.read_actual,Quad.tail_actual]
  have hz : Quad.read (links G 0) = 1 := by simp [links,Quad.read]
  have hs : ContDiff ℝ ω (Quad.strokes (G := G) (r+2) []) := by
    simp only [Quad.strokes]
    exact (Quad.tailMat_diff _).comp Quad.readMat_diff
  rw [he]
  refine ⟨hs.comp hm,?_⟩
  simpa only [List.length_nil,Nat.sub_zero] using (Quad.strokes_flat (r+2) [] (links G) hm hz)

theorem estimates (G : Gauge) (r : ℕ) : ∃ M > 0, ∀ j ≤ r+3, ∀ x : Quad.Dir G,
    ‖x‖ ≤ 1 → ‖iteratedFDeriv ℝ j (row G r) x‖ ≤ M * ‖x‖ ^ (r+3-j) := by
  obtain ⟨hs,hf⟩ := jet G r
  obtain ⟨c,hc⟩ := (isCompact_closedBall (0:Quad.Dir G) 1).bddAbove_image
    (hs.continuous_iteratedFDeriv (m := r+3) le_top).norm.continuousOn
  refine ⟨max 1 c,lt_of_lt_of_le zero_lt_one (le_max_left ..),hf.bound hs ?_ (by positivity)⟩
  intro x hx
  exact (hc (Set.mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hx))).trans (le_max_right ..)

def localField (B : fieldDir G n 1) (p : Cell n) : Quad.Dir G := collect G B ∘ edges p

theorem physical (B : fieldDir G n 1) (p : Cell n) (r : ℕ) (t : ℝ) :
    row G r (t • localField B p) = leftOver (r+2) p (FundedWilsonGerm.ray B t) := by
  have h : links G (t • localField B p) = FundedWilsonGerm.ray B t ∘ edges p := by
    funext i
    change G.lieExp _ = G.lieExp _ * 1
    rw [mul_one]
    rfl
  simp only [row,h,read_edges,leftOver]

/-- Every actual paid face has an O(t^(r+1)) remainder on its own
normalized support after the original β=t⁻² variation. -/
theorem normalized (G : Gauge) (r : ℕ) : ∃ M > 0, ∀ (n : Side) (B : fieldDir G n 1)
    (p : Cell n), ‖localField B p‖ ≤ 1 → ∀ t : ℝ, t ≠ 0 → ‖t‖ ≤ 1 →
    ‖(t^2)⁻¹ * leftOver (r+2) p (FundedWilsonGerm.ray B t)‖ ≤ M * ‖t‖^(r+1) := by
  obtain ⟨M,hM,h⟩ := estimates G r
  refine ⟨M,hM,fun n B p hB t ht h₁ => ?_⟩
  have hx : ‖t • localField B p‖ ≤ ‖t‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) hB
  have he := h 0 (Nat.zero_le _) (t • localField B p) (hx.trans h₁)
  have hu : ‖row G r (t • localField B p)‖ ≤ M * ‖t‖^(r+3) := by
    have he' : ‖row G r (t • localField B p)‖ ≤ M * ‖t • localField B p‖^(r+3) := by
      simpa only [norm_iteratedFDeriv_zero,Nat.sub_zero] using he
    exact he'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hM.le)
  rw [← physical B p r t,norm_mul,norm_inv,norm_pow]
  calc
    (‖t‖^2)⁻¹ * ‖row G r (t • localField B p)‖ ≤ (‖t‖^2)⁻¹ * (M * ‖t‖^(r+3)) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = M * ‖t‖^(r+1) := by
      have hz : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
      rw [show r+3 = (r+1)+2 by omega,pow_add]
      field_simp

end YM.Integration.WilsonLimitConstruction.FundedWilsonStartupTail
end
