import YM.Integration.WilsonWalkMatrixBias
import YM.Comparison.Stencils.PathSeries

/-! Signed vector bias of the original transported plaquette curvature under
the physical conditional. The genuine approach path is traversed twice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWalkEndpointBias
open RG Lattice Wilson MeasureTheory Filter
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open FullQLocal.RenderedStep MatchingLedger.Compass.Income
open Comparison.Stencils
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical

variable {G : Gauge} {c f : Side}

/-- The original periodic slot is the fixed linear curvature projection of
the signed matrix holonomy of its entire closed walk. -/
theorem atSite_reads (s : Slot) (U : Config G c) (x : Site c) :
    s.atSite U x = Pert.First.recoverL G (G.mat (travel U x (closes s))) := by
  have ht : travel (expandAt x U) 0 (closes s) = travel U x (closes s) := by
    rw [travel_at, map_zero, zero_add]
  rw [←ht,closes,travel_append,travel_append,stop_append,square_stop,travel_reverse]
  unfold Slot.atSite Slot.eval
  rw [←G.curvature_conjugate,Pert.First.recover_group]
  rfl

/-- The normalized original Lie projection has an explicit Frobenius bound. -/
theorem recover_bound (A : G.Mat) : ‖Pert.First.recoverL G A‖ ≤ (1/G.colorScale)*‖A‖ := by
  change ‖G.projectColor ((1/2:ℝ) • (A-star A))‖ ≤ _
  calc
    _ ≤ ‖(1/2:ℝ) • (A-star A)‖ / G.colorScale := G.project_norm _
    _ ≤ ‖A‖ / G.colorScale := by
      apply div_le_div_of_nonneg_right _ G.colorScale_pos.le
      rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      have h := norm_sub_le A (star A)
      rw [norm_star] at h
      linarith
    _ = _ := by ring

variable (S : StepData c f)

/-- The signed holonomy itself has the dimension-normalized branch bound. -/
theorem matrix_conditional (b : ℝ) (Q : Config G c) (x : Site c) (w : Walk) :
    ‖(∫ V, S.noise b Q V • G.mat (travel V x w) ∂prior G c)-G.mat (travel Q x w)‖ ≤
      (w.length:ℝ)^2*(G.repDim:ℝ)*WilsonLinkEnergy.energy S G b := by
  apply (WilsonWalkMatrixBias.conditional S (ContinuousLinearMap.id ℝ G.Mat) 1 zero_le_one
    (fun X => by change ‖X‖ ≤ (1:ℝ)*‖X‖; rw [one_mul]) b Q x w).trans_eq
  rw [one_mul]

/-- On the original funded calendar the simultaneous estimate also holds in
the full Frobenius matrix norm before any color projection. -/
theorem matrix_selected (R : Run G) (hG : G.Simple) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      ∀ (x : Site (R.family.side m p)) (w : Walk) (U : Config G (R.family.side (m+1) p)),
      let S := R.family.path.levels.clock.op m p
      let β := R.family.path.β N p (m+1)
      ‖(∫ V, S.density β U V • G.mat (travel V x w) ∂prior G _) -
        ∑ z, S.likelihood U z • G.mat (travel (S.prediction U z) x w)‖ ≤
        C*(w.length:ℝ)^2*(regulatorRun R.family N p (m+1))^2 := by
  exact
    WilsonWalkMatrixBias.selected R hG (ContinuousLinearMap.id ℝ G.Mat) 1 zero_le_one
      (fun X => by change ‖X‖ ≤ (1:ℝ)*‖X‖; rw [one_mul])

/-- Signed error for an individual true branch and any transported plaquette. -/
theorem conditional (b : ℝ) (Q : Config G c) (s : Slot) (x : Site c) :
    ‖(∫ V, S.noise b Q V • s.atSite V x ∂prior G c) - s.atSite Q x‖ ≤
      (1/G.colorScale) * ((s.length+s.walk.length:ℕ):ℝ)^2 *
        (G.repDim:ℝ)*WilsonLinkEnergy.energy S G b := by
  simpa only [atSite_reads, cost_path] using
    WilsonWalkMatrixBias.conditional S (Pert.First.recoverL G) (1/G.colorScale) (div_nonneg zero_le_one G.colorScale_pos.le) recover_bound b Q x (closes s)

/-- The original predicted curvature and its measured value retain the sign
and all color coordinates in the genuine mixture of branches. -/
theorem mixture (b : ℝ) (h : S.patch.Branches S.kernel G) (U : Config G f) (s : Slot) (x : Site c) :
    ‖(∫ V, S.density b U V • s.atSite V x ∂prior G c) -
       ∑ z, S.likelihood U z • s.atSite (S.prediction U z) x‖ ≤
      (1/G.colorScale) * ((s.length+s.walk.length:ℕ):ℝ)^2 *
        (G.repDim:ℝ)*WilsonLinkEnergy.energy S G b := by
  simpa only [atSite_reads, cost_path] using
    WilsonWalkMatrixBias.mixture S (Pert.First.recoverL G) (1/G.colorScale) (div_nonneg zero_le_one G.colorScale_pos.le) recover_bound b h U x (closes s)

/-- A single original regulator tail bounds every selected physical branch
mixture and every transported plaquette, including moving slots. -/
theorem selected (R : Run G) (hG : G.Simple) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      ∀ (x : Site (R.family.side m p)) (s : Slot) (U : Config G (R.family.side (m+1) p)),
      let S := R.family.path.levels.clock.op m p
      let β := R.family.path.β N p (m+1)
      ‖(∫ V, S.density β U V • s.atSite V x ∂prior G _) -
          ∑ z, S.likelihood U z • s.atSite (S.prediction U z) x‖ ≤
        C*((s.length+s.walk.length:ℕ):ℝ)^2*(regulatorRun R.family N p (m+1))^2 := by
  obtain ⟨C,hC,H⟩ := WilsonWalkMatrixBias.selected R hG (Pert.First.recoverL G) (1/G.colorScale) (div_nonneg zero_le_one G.colorScale_pos.le) recover_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with m hm N p hN x s U
  simpa only [atSite_reads,cost_path] using hm N p hN x (closes s) U

end YM.Integration.WilsonWalkEndpointBias
end
