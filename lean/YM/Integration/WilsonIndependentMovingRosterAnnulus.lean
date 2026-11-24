import YM.Integration.WilsonIndependentMovingRosterNormalizedRead

/-! Clearance at the two physical scales from the normalized far support and the retained near radii. -/
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterAnnulus
open WilsonCoeffUV WilsonCoeffUV.Mer
open Filter Function Metric
open scoped Topology

theorem original {n D:ℕ}(φ:Fin n→Rarity D)(ψ:Rarity D)(T d z y:ℝ)
    (positive:0<T)(near:∀s,(φ s).radius≤z)(remote:∀q∈tsupport ψ.ψ.val,d≤‖q‖)
    (scale:max z (1+|y|)≤T*(d/2)):
    (∀s,∀p∈tsupport (φ s).ψ.val,∀q∈tsupport ψ.ψ.val,T*(d/2)≤dist p (T • q)) ∧
      (∀q∈tsupport ψ.ψ.val,T*(d/2)+1+|y|≤‖T • q‖):=by
  have radius (q:Point4)(hq:q∈tsupport ψ.ψ.val):T*d≤‖T • q‖:=by
    rw [norm_smul,Real.norm_of_nonneg positive.le]
    exact mul_le_mul_of_nonneg_left (remote q hq) positive.le
  constructor
  · intro s p hp q hq
    have inside:dist p (0:Point4)≤(φ s).radius:=Metric.mem_closedBall.mp ((φ s).support hp)
    have tri:=dist_triangle (0:Point4) p (T • q)
    rw [dist_zero_left,dist_comm (0:Point4) p] at tri
    linarith only [inside,near s,(le_max_left z (1+|y|)).trans scale,radius q hq,tri]
  · intro q hq
    linarith only [(le_max_right z (1+|y|)).trans scale,radius q hq]

end YM.Integration.WilsonIndependentMovingRosterAnnulus
