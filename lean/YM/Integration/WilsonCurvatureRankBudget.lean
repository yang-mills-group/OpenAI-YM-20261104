import YM.Integration.WilsonCurvatureEndpoints

/-! A per-source invoice at each genuine curvature rank. All native path-length payments and coupling powers remain in the integrals. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCurvatureRankBudget
open MeasureTheory Filter Set Finset Lattice Wilson RG Marker OPE.Therm
open Comparison.Density.RenderM LocalComparison LocalComparison.MarkedPackets Push.AbsoluteSums
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V]
variable {R : Census V} {D : V → ComparisonDensity.Address.Orbit}
variable (P : MarkedPackets D G n R) (μ : Measure (Config G n)) (w : V → ℝ)
variable (g width : ℝ) (x : IndependentTests D)

def invoice (v : V) (q i : ℕ) : ℝ :=
  if v ∈ (P.mode i).val ∧ P.rank i = q then
    match P.packet i with
    | none => 0
    | some T => Poly.toll w (P.mode i) * Real.exp (width*T.fall) *
      ∫ U, ‖P.term (testInclusion D x) g U i‖ ∂μ
  else 0

variable {P μ w g width} {p : BudgetPoint} {address : V → Support n} {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
variable {budget : ℝ} {coverOffset coverSlope : ℕ}

omit [Fintype V] in
theorem paid [IsProbabilityMeasure μ]
    (H : P.Paid p address region w g width budget coverOffset coverSlope)
    (v : V) (q : ℕ) (t δ : ℝ) (ht : 0 ≤ t) (hd : 0 ≤ δ)
    (rare : ∀ z : Face (Per n), μ.real (trigger z t) ≤ δ) :
    SumBudget (invoice P μ w g width x v q) ((t^q+2^q*((q:ℝ)*δ))*budget) := by
  have eps : 0 ≤ t^q+2^q*((q:ℝ)*δ) := by positivity
  apply budget_mono (budget_scale eps (H.roots v))
  · intro i
    unfold invoice
    split
    · cases hi : P.packet i with
      | none => exact le_rfl
      | some T =>
        exact mul_nonneg (mul_nonneg (Poly.worth H.positive _).le (Real.exp_pos _).le)
          (integral_nonneg fun _ => norm_nonneg _)
    · exact le_rfl
  · intro i
    by_cases he : v ∈ (P.mode i).val ∧ P.rank i = q
    · obtain ⟨hv,hq⟩ := he
      cases hi : P.packet i with
      | none => simp [invoice,hv,hq,hi]
      | some T =>
        simp only [invoice,hv,hq,hi,eq_self, and_self,ite_true]
        have eqn : (∫ U, ‖P.term (testInclusion D x) g U i‖ ∂μ) =
            ‖(g:ℂ)^P.power i‖*(∫ U, ‖T.read (testInclusion D x) U‖ ∂μ) := by
          simp only [term,hi,norm_mul,integral_const_mul]
        have hcost := WilsonCurvatureEndpoints.measured T (testInclusion D x) ((H.coefficient i T hi).2 x) μ t δ ht rare
        have heps := congrArg (fun k : ℕ => t^k+2^k*((k:ℝ)*δ)) hq
        rw [heps] at hcost
        rw [eqn]
        calc _ ≤ Poly.toll w (P.mode i)*Real.exp (width*T.fall) *
                (‖(g:ℂ)^P.power i‖*(T.coin*(t^q+2^q*((q:ℝ)*δ)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcost (norm_nonneg _))
                (mul_nonneg (Poly.worth H.positive _).le (Real.exp_pos _).le)
             _ = _ := by ring
    · have h := mul_nonneg eps ((H.roots v).1 i)
      simpa only [invoice,he,ite_false] using h

omit [Fintype V] in
theorem original {H : History G} (Y : H.Selected) (θ : Poetry H.levels) (hG : G.Simple) :
    ∀ᶠ k : ℕ in atTop, ∀ N, k ≤ N → ∀ (p : ℕ)
      (P : MarkedPackets D G (H.S.side k p) R) (β : BudgetPoint)
      (addr : V → Support (H.S.side k p)) (region : Comparison.Density.Testing.Region (fun v => (D v).Mood) (H.S.side k p))
      (w : V → ℝ) (g width budget : ℝ) (off slope : ℕ),
      P.Paid β addr region w g width budget off slope →
      ∀ (x : IndependentTests D) (v : V) (q : ℕ),
        SumBudget (invoice P (scene H N p k) w g width x v q)
          (((cool H.levels k)^q+2^q*((q:ℝ)*vanishP H.levels k))*budget) := by
  filter_upwards [rare θ hG Y] with k hk
  intro N hN p P β addr region w g width budget off slope hP x v q
  letI := probability (H:=H) (p:=p) Y hN
  apply paid x hP v q _ _ _ (Real.exp_pos _).le (hk N hN p)
  unfold cool Calendar.hatCoupling
  positivity

end YM.Integration.WilsonCurvatureRankBudget
end
