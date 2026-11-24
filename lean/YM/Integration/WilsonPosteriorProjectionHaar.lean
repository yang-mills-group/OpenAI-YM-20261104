import YM.Integration.WilsonPosteriorProjectionConditional

/-! The measured angular response is the unconditional tag sum divided by
the actual fine-vacuum push in the moving Haar primitive. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionHaar
open Finset Set MeasureTheory Lattice Wilson RG RG01.Kernel
open scoped BigOperators Classical
variable {G : Gauge} (H : History G) (sel : H.Selected) {N n m : ℕ} (hm : m<N)
variable (φ : Config G (H.S.side (m+1) n) → ℝ)

def posterior (V : Config G (H.S.side m n)) :=
  let S := H.levels.clock.op m n
  let R := H.rep N n (m+1)
  S.push R.beta (fun U => φ U * R.eval U) V / S.push R.beta R.eval V

include sel hm in
theorem normalized {b : ℝ}
    (funded : Bounded (prior G (H.S.side (m+1) n))
      (fun (_ : (H.levels.clock.op m n).Choices) U => ((φ U : ℝ) : ℂ)) b)
    (V : Config G (H.S.side m n)) :
    conditional H N m n V (fun _ U => ((φ U : ℝ) : ℂ)) = (posterior H (N:=N) φ V : ℂ) := by
  let S := H.levels.clock.op m n
  let R := H.rep N n (m+1)
  let D := (H.rep N n m).eval V
  let μ := prior G (H.S.side (m+1) n)
  let w := expense H N m n V
  have cal := RG01.Kernel.actual N H sel V hm
  have cost (i : S.Choices) : Integrable (fun U => w i U * φ U) μ := by
    have paid := (cal.funds funded i).re
    simpa only [← Complex.ofReal_mul,RCLike.re_eq_complex_re,Complex.ofReal_re] using paid
  have mass : D = S.push R.beta R.eval V := congrFun (sel.steps N n m hm).1 V
  unfold conditional RG01.Kernel.moment
  change (∑ i : S.Choices, ∫ U, (w i U : ℂ) * (φ U : ℂ) ∂μ) = _
  simp_rw [← Complex.ofReal_mul,integral_complex_ofReal]
  rw [← Complex.ofReal_sum,Complex.ofReal_inj,← integral_finsetSum univ (fun i _ => cost i)]
  change (∫ U, ∑ i : S.Choices, w i U * φ U ∂μ) =
    S.push R.beta (fun U => φ U * R.eval U) V / S.push R.beta R.eval V
  rw [← mass]
  unfold StepData.push
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with U
  change (∑ i : S.Choices, (S.likelihood U i * S.noise R.beta (S.prediction U i) V *
    R.eval U / D) * φ U) = ((∑ i : S.Choices, S.likelihood U i *
      S.noise R.beta (S.prediction U i) V) * (φ U * R.eval U)) / D
  simp only [sum_mul,sum_div]
  apply sum_congr rfl
  intro i _
  ring

end YM.Integration.WilsonPosteriorProjectionHaar

