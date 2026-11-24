import YM.RGComparison.Core16.Leading

/-! The leading normalized conditional coefficient on the whole retained descent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesDescentPrincipal
open Lattice RG Tree Wilson Precision Push.BetaTransport PertExtension PertExtension.Series Tested Radial GaussianScore
open RGComparison.Core16 RGComparison.Core16.Descent
open Function MeasureTheory
open scoped Topology ContDiff BigOperators Classical

variable {G : Gauge} {n c : Side} {d : Descent n c}

/-- The first surviving coefficient of the true full finite descent is the
normalized Gaussian average of the literal microscopic field jet. The patch
tags use a common quadratic form and the original vacuum normalization. -/
theorem gaussian (P : ChartRatio G) (chart : LocalRatio P) (room : d.Room G)
    (t : d.Tags) (u : ℕ → ℝ) {f : Config G n → ℝ} (test : d.Testable f)
    {w : ℕ} (grade : d.grade f w) :
    ranking P d u f w = (ambient t room).average (Chart.tangent G d.Links)
      (Radial.jet (f ∘ d.fine 1 ∘ d.tablePath) w) := by
  let K := (ambient t room).kern
  let A := Radial.jet (f ∘ d.fine 1 ∘ d.tablePath) w
  let μ := Chart.tangent G d.Links
  let fee : ℝ := Chart.jacobian P (U:=d.Links) 0 * (Fintype.card d.Tags : ℝ)⁻¹
  let mass : ℝ := ∑ _ : d.Tags, fee
  have kernel (b : d.Tags) : Radial.kernel (d.phase G b) = K := by
    rw [kern_is b room]
    funext x
    change Real.exp (-((Descent.quadratic G d b) x x) / 2) = Real.exp (-((Descent.quadratic G d t) x x) / 2)
    rw [quadratic_independent b t room]
  have top (b : d.Tags) : gaussianTerm P b (d.resetTerms u f b) w =
      fee * ∫ x, A x * K x ∂μ := by
    unfold gaussianTerm Radial.moment Radial.normTerm
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [ordinary_grade_jet b P chart test grade u room x, kernel b]
    exact mul_assoc ..
  have bottom (b : d.Tags) : gaussianTerm P b (d.resetTerms u 1 b) 0 =
      fee * ∫ x, K x ∂μ := by
    rw [first_gaussian P b _ (room_ok d room),reset_flat_value u (room_ok d room) b, kernel b]
    simp [fee,μ]
  have num : bareRank P d u f w = mass * ∫ x, A x * K x ∂μ := by
    rw [bareRank,Finset.sum_apply,Finset.sum_mul]
    exact Finset.sum_congr rfl (fun b _ => top b)
  have den : bareRank P d u 1 0 = mass * ∫ x, K x ∂μ := by
    rw [bareRank,Finset.sum_apply,Finset.sum_mul]
    exact Finset.sum_congr rfl (fun b _ => bottom b)
  have positive := pivot P chart u room
  rw [den] at positive
  have hm := (mul_ne_zero_iff.mp positive.ne').1
  have hk := (mul_ne_zero_iff.mp positive.ne').2
  have coefficient : ranking P d u f w = bareRank P d u f w * (bareRank P d u 1 0)⁻¹ := by
    unfold ranking Tested.divide Tested.term
    rw [PowerSeries.coeff_mul,Finset.sum_eq_single_of_mem (w,0) (Finset.mem_antidiagonal.mpr (add_zero w))]
    · simp only [PowerSeries.coeff_mk,PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.constantCoeff_inv]
      rfl
    intro j hj hjw
    have hi := Finset.mem_antidiagonal.mp hj
    rw [PowerSeries.coeff_mk,field_rank_zero P chart room u test grade j.1 (by
      by_contra! hn
      apply hjw
      exact Prod.ext (by omega) (by omega)),zero_mul]
  rw [coefficient,num,den]
  change mass * (∫ x, A x * K x ∂μ) * (mass * ∫ x, K x ∂μ)⁻¹ =
    (∫ x, A x * K x ∂μ) / ∫ x, K x ∂μ
  field_simp

end YM.Integration.WilsonMatrixTicketLanesDescentPrincipal
