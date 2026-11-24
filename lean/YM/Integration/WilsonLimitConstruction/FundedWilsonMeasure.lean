import YM.Integration.WilsonLimitConstruction.FundedWilsonHaar
import YM.Integration.WilsonLimitConstruction.FundedWilsonBoundary

/-! The product Haar Jacobian and the regularized Wilson action on the
same finite chart. The signed observable stays in its original field.
Every normalized link direction uses one volume-independent local series. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonMeasure

open Filter Set Metric Lattice Wilson RG Exterior PertExtension
open PhysicalNext.Repeat.Legato FundedWilsonGerm
open scoped Topology BigOperators ContDiff NNReal ENNReal
variable {G : Gauge} {n : Side}

def priorWeight (B : fieldDir G n 1) (t : ℝ) :=
  Chart.jacobian (XSpace.Bare.chart G) (t • collect G B)

def gas {B : fieldDir G n 1} (C : Curve B) (P : ℝ → ℝ) (t : ℝ) :=
  Real.exp (-corrected C P t)

def density {B : fieldDir G n 1} (C : Curve B) (P : ℝ → ℝ) (t : ℝ) :=
  priorWeight B t * gas C P t

theorem chart_integrand {B : fieldDir G n 1} (C : Curve B) (P : ℝ → ℝ)
    (O : Config G n → ℝ) {t : ℝ} (ht : t ≠ 0) :
    FundedWilsonHaar.integrand ((t^2)⁻¹ + P t) O (t • collect G B) =
      density C P t * O (ray B t) := by
  have hx : Chart.expLinks G (Edge (Site n)) (t • collect G B) = ray B t := by
    funext e
    change G.lieExp _ = G.lieExp _ * 1
    rw [mul_one]
    rfl
  unfold FundedWilsonHaar.integrand density priorWeight gas
  rw [hx]
  dsimp only
  rw [exact_bare C P ht,mul_assoc]

theorem original (R : Run G) (N p : ℕ) {B : fieldDir G (R.family.side N p) 1}
    (C : Curve B) (P : ℝ → ℝ) {t : ℝ} (ht : t ≠ 0)
    (hβ : (t^2)⁻¹ + P t = R.family.beta N p) :
    density C P t =
      priorWeight B t * (R.family.path.rep N p N).eval (ray B t) := by
  unfold density gas
  rw [FundedWilsonBoundary.funded R N p B C P ht hβ]

theorem prior_analytic (B : fieldDir G n 1) : AnalyticAt ℝ (priorWeight B) 0 := by
  have ha : ContDiffAt ℝ ω (fun t : ℝ => t • collect G B) 0 := by fun_prop
  exact (FundedWilsonHaar.analytic_jacobian G n).comp_of_eq ha.analyticAt (by simp)

theorem gas_analytic {B : fieldDir G n 1} (C : Curve B) {P : ℝ → ℝ}
    (hP : AnalyticAt ℝ P 0) : AnalyticAt ℝ (gas C P) 0 :=
  (corrected_analytic C hP).neg.rexp

theorem joint {B : fieldDir G n 1} (C : Curve B) {P : ℝ → ℝ}
    (hP : AnalyticAt ℝ P 0) : AnalyticAt ℝ (density C P) 0 :=
  (prior_analytic B).fun_mul (gas_analytic C hP)

theorem coefficient {B : fieldDir G n 1} (C : Curve B) {P : ℝ → ℝ}
    (hP : AnalyticAt ℝ P 0) (k : ℕ) :
    iteratedDeriv k (density C P) 0 = ∑ i ∈ Finset.range (k+1),
      (k.choose i : ℝ) * iteratedDeriv i (priorWeight B) 0 *
        iteratedDeriv (k-i) (gas C P) 0 := by
  exact iteratedDeriv_fun_mul (prior_analytic B).contDiffAt (gas_analytic C hP).contDiffAt

/-- The original one-link fee has a common radius, operator bound and
geometric remainder. All are chosen before counting physical links. -/
theorem link (G : Gauge) : ∃ (p : FormalMultilinearSeries ℝ G.Color ℝ) (r : ℝ≥0),
    0 < r ∧ HasFPowerSeriesOnBall (Chart.fee (XSpace.Bare.chart G)) p 0 r ∧
    (∃ M > 0, ∀ k, ‖p k‖ * (r:ℝ)^k ≤ M) ∧
    ∀ s : ℝ≥0, s < r → ∃ a ∈ Ioo (0:ℝ) 1, ∃ A > 0,
      ∀ x : G.Color, ‖x‖ < s → ∀ k,
        ‖Chart.fee (XSpace.Bare.chart G) x - p.partialSum k x‖ ≤ A * (a * (‖x‖ / s))^k := by
  obtain ⟨p,R,h⟩ := (Chart.Ratio.fee_smooth (XSpace.Bare.chart_ratio G)).analyticAt
  obtain ⟨r,hr,hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h.r_pos
  obtain ⟨M,hM,hb⟩ := p.norm_mul_pow_le_of_lt_radius (hrR.trans_le h.r_le)
  have hd := h.mono hr hrR.le
  refine ⟨p,r,ENNReal.coe_pos.mp hr,hd,⟨M,hM,hb⟩,fun s hs => ?_⟩
  obtain ⟨a,ha,A,hA,h⟩ := h.uniform_geometric_approx' ((ENNReal.coe_lt_coe.mpr hs).trans hrR)
  exact ⟨a,ha,A,hA,fun x hx k => by
    simpa only [zero_add] using h x (mem_ball_zero_iff.mpr hx) k⟩

end YM.Integration.WilsonLimitConstruction.FundedWilsonMeasure
end
