import YM.Integration.WilsonLimitConstruction.FundedWilsonPlaquette
import YM.Integration.WilsonLimitConstruction.FundedWilsonGerm

/-! The complex expansion is assembled from the four actual links of
each original Wilson plaquette. One radius controls every cutoff and
period for normalized plaquette directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonAtlas

open Filter Set Metric Lattice Exterior MS.Native
open FundedWilsonPlaquette
open scoped Topology ContDiff NNReal ENNReal BigOperators
variable {G : Gauge} {n : Side}

def directions (B : fieldDir G n 1) (i : Chart.Rout (Site n)) : Axis → G.Color :=
  collect G B ∘ Chart.loadC (Chart.drive n) i

theorem physical (B : fieldDir G n 1) (t : ℝ) :
    FundedWilsonGerm.action B t = ∑ i, price (t • directions B i) := by
  rw [FundedWilsonGerm.chart,Chart.rent,←Finset.sum_neg_distrib]
  rfl

def complexEnergy (S : Sheet G) (B : fieldDir G n 1) (z : ℂ) : ℂ :=
  ∑ i, (complexSeries S (directions B i)).sum z

theorem real_axis (S : Sheet G) (B : fieldDir G n 1) (hB : ∀ i, ‖directions B i‖ ≤ 1)
    {t : ℝ} (ht : ‖t‖ < (S.radius:ℝ)) :
    complexEnergy S B (t:ℂ) = FundedWilsonGerm.action B t := by
  rw [physical]
  push_cast
  exact Finset.sum_congr rfl fun i _ => FundedWilsonPlaquette.real_axis S (hB i) ht

theorem holomorphic (S : Sheet G) (B : fieldDir G n 1) (hB : ∀ i, ‖directions B i‖ ≤ 1) :
    AnalyticOnNhd ℂ (complexEnergy S B) (Metric.eball 0 S.radius) := by
  intro z hz
  exact Finset.analyticAt_fun_sum _ fun i _ => (complex_disc S (hB i)).analyticAt_of_mem hz

theorem projector (S : Sheet G) (B : fieldDir G n 1) (hB : ∀ i, ‖directions B i‖ ≤ 1)
    (k : ℕ) : iteratedDeriv k (complexEnergy S B) 0 / (k.factorial:ℂ) =
      ∑ i, (coefficient S (directions B i) k : ℂ) := by
  unfold complexEnergy
  rw [iteratedDeriv_fun_sum (fun i _ => (complex_disc S (hB i)).analyticAt.contDiffAt),Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => FundedWilsonPlaquette.projector S (hB i) k

private theorem real_disc (S : Sheet G) {a : Axis → G.Color} (ha : ‖a‖ ≤ 1) :
    HasFPowerSeriesOnBall (fun t : ℝ => price (t • a))
      (FormalMultilinearSeries.ofScalars ℝ (coefficient S a)) 0 S.radius := by
  refine ⟨FormalMultilinearSeries.le_radius_of_bound _ S.constant (fun k => ?_),
    ENNReal.coe_pos.mpr S.radius_pos, fun {t} ht => ?_⟩
  · simpa only [FormalMultilinearSeries.ofScalars_norm] using coefficient_bound S ha k
  · have ht' : ‖t‖ < (S.radius:ℝ) := by
      simpa only [Metric.eball_coe,Metric.mem_ball,dist_zero_right] using ht
    have hv : ‖t • a‖ < (S.radius:ℝ) := by
      rw [norm_smul]
      exact (mul_le_of_le_one_right (norm_nonneg _) ha).trans_lt ht'
    have h := S.realSeries.hasSum (y := t • a)
      (by simpa only [Metric.eball_coe,Metric.mem_ball,dist_zero_right] using hv)
    have hterm (k : ℕ) : S.series k (fun _ => t • a) = t^k * coefficient S a k := by
      simpa [coefficient,smul_eq_mul] using
        (S.series k).toMultilinearMap.map_smul_univ (fun _ : Fin k => t) (fun _ => a)
    simpa only [hterm, FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,
      zero_add,mul_comm] using h

theorem shifted (S : Sheet G) (B : fieldDir G n 1) (hB : ∀ i, ‖directions B i‖ ≤ 1)
    (C : FundedWilsonGerm.Curve B) (k : ℕ) :
    iteratedDeriv k C.value 0 / (k.factorial:ℝ) = ∑ i, coefficient S (directions B i) (k+2) := by
  rw [FundedWilsonGerm.coefficient C,funext (physical B),
    iteratedDeriv_fun_sum (fun i _ => (real_disc S (hB i)).analyticAt.contDiffAt),Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := (real_disc S (hB i)).hasFPowerSeriesAt
  have he := h.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries h
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff (k+2)) he

/-- The four-link error estimate has a single radius and geometric constant,
for every field, lattice, plaquette and truncation order. -/
theorem local_tail (S : Sheet G) {r : ℝ≥0} (hr : r < S.radius) :
    ∃ a ∈ Ioo (0:ℝ) 1, ∃ C > 0, ∀ x : Axis → G.Color, ‖x‖ < r → ∀ k,
      ‖price x - S.series.partialSum k x‖ ≤ C * (a * (‖x‖ / r)) ^ k := by
  obtain ⟨a,ha,C,hC,h⟩ := S.realSeries.uniform_geometric_approx' (ENNReal.coe_lt_coe.mpr hr)
  exact ⟨a,ha,C,hC,fun x hx k => by
    simpa only [zero_add] using h x (mem_ball_zero_iff.mpr hx) k⟩

end YM.Integration.WilsonLimitConstruction.FundedWilsonAtlas
end
