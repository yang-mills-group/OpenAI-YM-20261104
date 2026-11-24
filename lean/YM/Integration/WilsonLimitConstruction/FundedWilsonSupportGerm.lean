import YM.Integration.WilsonLimitConstruction.FundedWilsonJointDisk

/-! The actual divided plaquette action on an arbitrary family of
physical plaquettes. Its real restriction retains all overlapping links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonSupportGerm

open Filter Finset Set Metric Lattice Wilson Exterior MS.Native
open FundedWilsonPlaquette FundedWilsonAtlas
open scoped Topology ContDiff NNReal ENNReal BigOperators
variable {G : Gauge} {n : Side}

def physical (B : fieldDir G n 1) (J : Finset (Chart.Rout (Site n))) (t : ℝ) :=
  ∑ i ∈ J, price (t • directions B i)

def energy (S : Sheet G) (B : fieldDir G n 1) (J : Finset (Chart.Rout (Site n))) (z : ℂ) :=
  ∑ i ∈ J, (complexSeries S (directions B i)).sum z

theorem axis (S : Sheet G) (B : fieldDir G n 1) (J : Finset (Chart.Rout (Site n)))
    (hB : ∀ i ∈ J, ‖directions B i‖ ≤ 1) {t : ℝ} (ht : ‖t‖ < (S.radius:ℝ)) :
    energy S B J (t:ℂ) = (physical B J t : ℂ) := by
  unfold energy physical
  push_cast
  exact Finset.sum_congr rfl fun i hi => FundedWilsonPlaquette.real_axis S (hB i hi) ht

theorem holomorphic (S : Sheet G) (B : fieldDir G n 1) (J : Finset (Chart.Rout (Site n)))
    (hB : ∀ i ∈ J, ‖directions B i‖ ≤ 1) :
    AnalyticOnNhd ℂ (energy S B J) (Metric.eball 0 S.radius) := by
  intro z hz
  exact Finset.analyticAt_fun_sum _ fun i hi => (complex_disc S (hB i hi)).analyticAt_of_mem hz

theorem value_zero (B : fieldDir G n 1) (J : Finset (Chart.Rout (Site n))) :
    physical B J 0 = 0 := by
  simp [physical,price,Chart.gone,Chart.atCart]

theorem nonneg (B : fieldDir G n 1) (J : Finset (Chart.Rout (Site n))) (t : ℝ) :
    0 ≤ physical B J t := by
  apply Finset.sum_nonneg
  intro i _
  simpa only [price,Chart.gone,neg_neg] using
    (G.price_range (Chart.atCart (G.lieExp ∘ (t • directions B i)))).1

theorem divided (S : Sheet G) (B : fieldDir G n 1) (J : Finset (Chart.Rout (Site n)))
    (hB : ∀ i ∈ J, ‖directions B i‖ ≤ 1) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q (Metric.eball 0 S.radius) ∧
      (∀ z : ℂ, energy S B J z = z^2 * Q z) ∧
      ∀ (t : ℝ), t ≠ 0 → ‖t‖ < (S.radius:ℝ) →
        Q (t:ℂ) = (physical B J t / t^2 : ℝ) := by
  let E := energy S B J
  have hr : (0:ℝ) < S.radius := S.radius_pos
  have h0 : (0:ℂ) ∈ Metric.eball 0 S.radius := by simpa using hr
  have hE := holomorphic S B J hB
  have hc := (hE _ h0).differentiableAt.hasDerivAt.comp_ofReal (z := 0)
  have hz : E 0 = 0 := by
    simpa only [Complex.ofReal_zero,value_zero] using (axis S B J hB (t := 0) (by simpa using hr))
  have href : (fun t : ℝ => E (t:ℂ)) =ᶠ[𝓝 0] (fun t => (physical B J t : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hr] with t ht
    exact axis S B J hB (mem_ball_zero_iff.mp ht)
  have hmin : IsLocalMin (physical B J) 0 := by
    filter_upwards with t
    rw [value_zero]
    exact nonneg B J t
  have hreal : AnalyticAt ℝ (physical B J) 0 := by
    apply Finset.analyticAt_fun_sum
    intro i _
    change AnalyticAt ℝ (fun t : ℝ => price (t • directions B i)) 0
    have hx : AnalyticAt ℝ (fun t : ℝ => t • directions B i) 0 := by fun_prop
    exact S.realSeries.analyticAt.comp_of_eq hx (zero_smul _ _)
  have hd : deriv E 0 = 0 := by
    have h := hreal.differentiableAt.hasDerivAt.ofReal_comp
    rw [hmin.deriv_eq_zero,Complex.ofReal_zero] at h
    exact hc.unique (h.congr_of_eventuallyEq href)
  obtain ⟨Q,hQ,hf⟩ := (hE _ h0).exists_eq_sum_add_pow_mul 2
  have hfactor (z : ℂ) : E z = z^2 * Q z := by
    simpa [Finset.sum_range_succ,hz,hd,smul_eq_mul,E] using hf z
  refine ⟨Q,fun z hmem => ?_,hfactor,fun t ht htr => ?_⟩
  · by_cases hzero : z = 0
    · subst z; exact hQ
    apply ((hE z hmem).div (analyticAt_id.pow 2) (pow_ne_zero _ hzero)).congr
    filter_upwards [eventually_ne_nhds hzero] with w hw
    change E w / w^2 = Q w
    rw [hfactor w]
    field_simp
  · have hi := hfactor (t:ℂ)
    rw [show E (t:ℂ) = physical B J t from axis S B J hB htr] at hi
    push_cast
    apply (eq_div_iff (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ht))).mpr
    simpa [mul_comm] using hi.symm

end YM.Integration.WilsonLimitConstruction.FundedWilsonSupportGerm
end
