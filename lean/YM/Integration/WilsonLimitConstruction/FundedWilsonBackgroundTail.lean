import YM.Integration.WilsonLimitConstruction.FundedWilsonStartupTail
import YM.Integration.WilsonLimitConstruction.LocalUniformTaylor

/-! The actual Wilson plaquette on an arbitrary original four-link background.
All Taylor orders, including the scalar and linear sectors, are retained at
that background. The remainder is uniform over the compact physical group. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundTail

open Filter Function Lattice Wilson RG Exterior WilsonStartup Metric
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

def action (X : Quad.Space G) (a : Quad.Dir G) : ℝ :=
  1 - (Quad.readMat (Quad.spin a X)).trace.re / G.repDim

theorem smooth (G : Gauge) : ContDiff ℝ ω (uncurry (action (G:=G))) := by
  have hs := (Quad.spin_diff (G:=G)).comp (contDiff_snd.prodMk contDiff_fst)
  have hr := (Quad.readMat_diff (G:=G)).comp hs
  exact contDiff_const.sub ((Complex.reCLM.contDiff.comp
    ((((Matrix.traceLinearMap _ ℂ ℂ).restrictScalars ℝ).toContinuousLinearMap.contDiff).comp hr)).div_const _)

theorem physical (U : Quad.Group G) (a : Quad.Dir G) :
    action (Quad.mat U) a = G.price (Quad.read (fun i => G.lieExp (a i) * U i)) := by
  have h : Quad.spin a (Quad.mat U) =
      Quad.mat (fun i => G.lieExp (a i) * U i) := funext fun i => (G.mat_mul ..).symm
  rw [action,h,Quad.read_actual]
  rfl

def remainder (d : ℕ) (X : Quad.Space G) : Quad.Dir G → ℝ :=
  action X - Work.G05.blockTaylor d (action X)

/-- One constant for all original backgrounds and all normalized independent
directions at a fixed order. Every derivative of the actual subtracted action
receives the corresponding power of the physical perturbation. -/
theorem bounds (G : Gauge) (d : ℕ) : ∃ C > 0, ∀ U : Quad.Group G,
    ∀ j ≤ d+1, ∀ a : Quad.Dir G, ‖a‖ ≤ 1 →
      ‖iteratedFDeriv ℝ j (remainder d (Quad.mat U)) a‖ ≤ C * ‖a‖^(d+1-j) := by
  have hm : Continuous (Quad.mat (G:=G)) := continuous_pi fun i =>
    G.continuous_mat.comp (continuous_apply i)
  obtain ⟨C,hC,h⟩ := LocalUniformTaylor.purchase (Set.range (Quad.mat (G:=G)))
    (isCompact_range hm) (action (G:=G)) (smooth G) d
  exact ⟨C,hC,fun U => h (Quad.mat U) ⟨U,rfl⟩⟩

theorem normalized (G : Gauge) (r : ℕ) : ∃ C > 0, ∀ (U : Quad.Group G) (a : Quad.Dir G),
    ‖a‖ ≤ 1 → ∀ t : ℝ, t ≠ 0 → ‖t‖ ≤ 1 →
      ‖(t^2)⁻¹ * remainder (r+2) (Quad.mat U) (t • a)‖ ≤ C * ‖t‖^(r+1) := by
  obtain ⟨C,hC,h⟩ := bounds G (r+2)
  refine ⟨C,hC,fun U a ha t ht h₁ => ?_⟩
  have hx : ‖t • a‖ ≤ ‖t‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) ha
  have he := h U 0 (Nat.zero_le _) (t • a) (hx.trans h₁)
  have hu : ‖remainder (r+2) (Quad.mat U) (t • a)‖ ≤ C * ‖t‖^(r+3) := by
    simp only [norm_iteratedFDeriv_zero,Nat.sub_zero] at he
    exact he.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hC.le)
  rw [norm_mul,norm_inv,norm_pow]
  calc
    _ ≤ (‖t‖^2)⁻¹ * (C * ‖t‖^(r+3)) := mul_le_mul_of_nonneg_left hu (by positivity)
    _ = C * ‖t‖^(r+1) := by
      have hz : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
      rw [show r+3 = (r+1)+2 by omega,pow_add]
      field_simp

end YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundTail
end
