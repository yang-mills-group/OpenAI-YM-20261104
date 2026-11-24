import YM.Work.F02
import YM.MatchingLedger.Mountain.Miner
import YM.Comparison.Density.Render.Valence
import YM.Comparison.RG02.Assembly.Shift

/-! Qualitative analyticity and valuation of the original countable atom sum.
Ranks and roots may vary. The exponential budget is the native atom budget;
no packet is discarded and no alternative analytic completion is chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace YM.Integration.NativeBoundedAtomSeries

open Function Filter Set Metric Lattice RG Wilson Precision Exterior
open Work.F02 MatchingLedger.Mountain
open Comparison.RG02.Assembly
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {ι : Type*} {G : Gauge} {n : Side} {rank : ι → ℕ} {cap k : ℕ} {width : ℝ}
variable (atom : (i : ι) → Atom G (rank i)) (root : ι → Site n)

/-- The unchanged real atom sum, including its individual roots. -/
def value (U : Config G n) : ℝ :=
  ∑' i, (atom i).unmasked U (root i)

private lemma budget_nonneg (i : ι) :
    0 ≤ (atom i).budget width := by
  unfold Atom.budget Atom.magnitude
  positivity

private def rankFactor (G : Gauge) (cap : ℕ) : ℝ :=
  (max 1 |slotConst G|) ^ cap

private lemma rankFactor_nonneg : 0 ≤ rankFactor G cap := by
  unfold rankFactor
  positivity

private lemma rankFactor_bound {i : ι} (h : rank i ≤ cap) :
    |slotConst G| ^ rank i ≤ rankFactor G cap := by
  exact (pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _).trans
    (pow_le_pow_right₀ (le_max_left _ _) h)

/-- Exponentially summable native budgets imply summability at every field. -/
theorem value_summable (hwidth : 0 < width)
    (hcap : ∀ i, rank i ≤ cap)
    (hbudget : Summable (fun i => (atom i).budget width))
    (U : Config G n) :
    Summable (fun i => (atom i).unmasked U (root i)) := by
  refine .of_norm_bounded (hbudget.mul_right ((2 : ℝ) ^ cap)) ?_
  intro i
  calc
    ‖(atom i).unmasked U (root i)‖
        ≤ (atom i).magnitude * (2 : ℝ) ^ rank i :=
      (atom i).unmasked_bound U (root i)
    _ ≤ (atom i).budget width * (2 : ℝ) ^ rank i :=
      mul_le_mul_of_nonneg_right ((atom i).lower_budget width hwidth) (by positivity)
    _ ≤ (atom i).budget width * (2 : ℝ) ^ cap :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) (hcap i)) (budget_nonneg atom i)

private lemma complex_analytic (hwidth : 0 < width)
    (hcap : ∀ i, rank i ≤ cap)
    (hbudget : Summable (fun i => (atom i).budget width))
    (U : Config G n) :
    AnalyticAt ℂ (fun M => ∑' i, atomExt (atom i) (root i) M) (physical U) := by
  refine analytic_series _ (radius_pos hwidth)
    (fun i => (atomExt_contDiff (atom i) (root i)).differentiable (by simp))
    (hbudget.mul_right (rankFactor G cap)) ?_
  intro i M hM
  refine (atomExt_bound (atom i) U hwidth M (ball_subset_closedBall hM) (root i)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (budget_nonneg atom i)
  exact (le_abs_self _).trans ((abs_pow ..).trans_le (rankFactor_bound (hcap i)))

private lemma complex_value (hwidth : 0 < width)
    (hcap : ∀ i, rank i ≤ cap)
    (hbudget : Summable (fun i => (atom i).budget width))
    (U : Config G n) :
    (∑' i, atomExt (atom i) (root i) (physical U)) =
      Complex.ofRealCLM (value atom root U) := by
  unfold value
  rw [Complex.ofRealCLM.map_tsum (value_summable atom root hwidth hcap hbudget U)]
  exact tsum_congr fun i => atomExt_physical (atom i) U (root i)

/-- Analyticity is for the original full field germ, not only a scalar ray. -/
theorem value_analytic (hwidth : 0 < width)
    (hcap : ∀ i, rank i ≤ cap)
    (hbudget : Summable (fun i => (atom i).budget width)) :
    ContDiffAt ℝ ω (fun v : fieldDir G n 1 => value atom root (represent v)) 0 := by
  let F : Ambient G n → ℂ := fun M => ∑' i, atomExt (atom i) (root i) M
  have hF : ContDiffAt ℝ ω F (physical (represent (0 : fieldDir G n 1))) :=
    (complex_analytic atom root hwidth hcap hbudget _).contDiffAt.restrict_scalars ℝ
  have hp (e : Edge (Site n)) :
      ContDiffAt ℝ ω (fun v : fieldDir G n 1 => G.mat (represent v e)) 0 := by
    simpa only [Miner.fortune, Lattice.pull_id] using
      (Miner.allows_signed (G := G) (n := n) 1 0 0
        (by simp : (0 : fieldDir G n 1) ∈ ball 0 1) e).analytic
  have he := Complex.reCLM.contDiff.contDiffAt.comp 0
    (hF.comp 0 (physical_contDiffAt hp))
  have hv (v : fieldDir G n 1) :
      Complex.reCLM (F (physical (represent v))) = value atom root (represent v) := by
    rw [show F (physical (represent v)) =
      Complex.ofRealCLM (value atom root (represent v)) from
      complex_value atom root hwidth hcap hbudget _]
    rfl
  simpa only [Function.comp_def, hv] using he

private def edgeCoordinates : fieldDir G n 1 →L[ℝ] Directions G n :=
  ContinuousLinearMap.pi fun e => ContinuousLinearMap.proj (e.1, coord e.2)

private lemma increment_edge (v : fieldDir G n 1) :
    increment 1 (edgeCoordinates v) = represent v := by
  funext e
  simp only [increment, edgeCoordinates, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply, Pi.one_apply, mul_one, Work.F03.represent_link]

/-- Each native atom retains its original rank valuation in the actual log chart. -/
theorem atom_vanish {t j : ℕ} (a : Atom G t) (o : Site n) (hj : j < t) :
    iteratedFDeriv ℝ j
      (fun v : fieldDir G n 1 => a.unmasked (represent v) o) 0 = 0 := by
  let f : Directions G n → ℝ := fun z => a.unmasked (increment 1 z) o
  have hf : ContDiffAt ℝ j f (edgeCoordinates (0 : fieldDir G n 1)) := by
    rw [map_zero]
    exact (Comparison.Density.Render.reserved a o
      (k := j) (x := 0) (by simp)).smooth
  have he : (fun v : fieldDir G n 1 => a.unmasked (represent v) o) =
      f ∘ edgeCoordinates := by
    funext v
    change _ = a.unmasked (increment 1 (edgeCoordinates v)) o
    rw [increment_edge]
  rw [he, contact_right edgeCoordinates hf, map_zero,
    show iteratedFDeriv ℝ j f 0 = 0 from
      Comparison.Density.Render.valuation a j hj o]
  rfl

/-- Uniform finite rank and the paid native path series preserve all lower jets. -/
theorem value_grade (hwidth : 0 < width)
    (hcap : ∀ i, rank i ≤ cap)
    (hbudget : Summable (fun i => (atom i).budget width))
    (hlower : ∀ i, k ≤ rank i) :
    GradeAt k (fun v : fieldDir G n 1 => value atom root (represent v)) := by
  refine ⟨value_analytic atom root hwidth hcap hbudget, ?_⟩
  intro j hj
  let C : ι → ℝ := fun i =>
    (atom i).budget width * (rankFactor G cap * Miner.richness G j width)
  have hC : Summable C :=
    hbudget.mul_right (rankFactor G cap * Miner.richness G j width)
  have hu (i : ι) (v : fieldDir G n 1) (hv : v ∈ ball 0 1) :
      Push.Uniform.Allows j (fun z => (atom i).unmasked (represent z) (root i)) v (C i) := by
    have ha := Miner.atoms (G := G) (n := n) 1 (root i) hwidth j hv (atom i)
    simp only [Miner.fortune, Lattice.pull_id] at ha
    refine ha.mono ?_
    unfold C Miner.value
    apply mul_le_mul_of_nonneg_left _ (budget_nonneg atom i)
    exact mul_le_mul_of_nonneg_right (rankFactor_bound (hcap i))
      (Miner.richness_pos G j hwidth).le
  unfold value
  rw [Push.Uniform.iterated_at_sum isOpen_ball
    (convex_ball (0 : fieldDir G n 1) 1).isPreconnected hC hu
    (by simp : (0 : fieldDir G n 1) ∈ ball 0 1) j le_rfl]
  simpa only [tsum_zero] using
    (tsum_congr fun i => atom_vanish (atom i) (root i) (hj.trans_le (hlower i)))

end YM.Integration.NativeBoundedAtomSeries
